(* ========================================================================= *)
(* 4CT/map_defs.ml                                                           *)
(*                                                                           *)
(* Maps of regions in the plane: definitions and elementary facts.  A map    *)
(* (plane_map) is a set of pairwise disjoint open connected regions of       *)
(* real^2; two regions are adjacent (adjacent_regions) when they share a     *)
(* border point that borders no third region (so meeting at a corner of      *)
(* three or more regions does not count), and map_colorable n M asks for a   *)
(* colouring with n colours giving adjacent regions different colours.       *)
(* These are simple_map, adjacent and colorable_with of Gonthier's           *)
(* realplane.v, with a map given as a set of regions instead of a partial    *)
(* equivalence relation on points.  The planar-graph four colour theorem     *)
(* enters as the hypothesis planar_graphs_four_colorable, discharged by      *)
(* FOUR_COLOR_PLANAR_GRAPH_OF_REDUCIBILITY in four_color_map.ml.  The chain  *)
(* is map_defs -> map_grid (ADJACENCY_GRAPH_PLANAR) -> map_main (finite      *)
(* maps, compactness, the theorem modulo planar graphs) -> four_color_map;   *)
(* up to map_main it needs only Multivariate and planar_graph.ml.            *)
(* ========================================================================= *)

needs "Autoformalization/planar_graph.ml";;
prioritize_num();;

let plane_map = new_definition
 `plane_map (M:(real^2->bool)->bool) <=>
    (!r. r IN M ==> open r /\ connected r) /\ pairwise DISJOINT M`;;

let adjacent_regions = new_definition
 `adjacent_regions (M:(real^2->bool)->bool) r1 r2 <=>
    r1 IN M /\ r2 IN M /\ ~(r1 = r2) /\
    ?z. z IN closure r1 INTER closure r2 /\
        !r. r IN M /\ z IN closure r ==> r = r1 \/ r = r2`;;

let map_colorable = new_definition
 `map_colorable n (M:(real^2->bool)->bool) <=>
    ?c:(real^2->bool)->num.
        (!r. r IN M ==> c r < n) /\
        (!r1 r2. adjacent_regions M r1 r2 ==> ~(c r1 = c r2))`;;

(* The four colour theorem for planar graphs, at the type of regions         *)
let planar_graphs_four_colorable = new_definition
 `planar_graphs_four_colorable <=>
    !(V:(real^2->bool)->bool) E.
        planar_graph V E
        ==> ?c:(real^2->bool)->num.
                (!v. v IN V ==> c v < 4) /\
                (!u v. {u,v} IN E ==> ~(c u = c v))`;;

(* ------------------------------------------------------------------------- *)
(* Elementary facts.                                                         *)
(* ------------------------------------------------------------------------- *)

(* adjacency in M implies adjacency in any subfamily containing both regions *)
let ADJACENT_REGIONS_SUBSET = prove
 (`!M M' r1 r2. M' SUBSET M /\ r1 IN M' /\ r2 IN M' /\ adjacent_regions M r1 r2
                ==> adjacent_regions M' r1 r2`,
  REWRITE_TAC[adjacent_regions; SUBSET] THEN MESON_TAC[]);;

let ADJACENT_REGIONS_SYM = prove
 (`!M r1 r2. adjacent_regions M r1 r2 <=> adjacent_regions M r2 r1`,
  REWRITE_TAC[adjacent_regions; IN_INTER] THEN MESON_TAC[]);;

let ADJACENT_REGIONS_NONEMPTY = prove
 (`!M r1 r2. adjacent_regions M r1 r2 ==> ~(r1 = {}) /\ ~(r2 = {})`,
  REWRITE_TAC[adjacent_regions; IN_INTER] THEN
  MESON_TAC[CLOSURE_EMPTY; NOT_IN_EMPTY]);;

let PLANE_MAP_SUBSET = prove
 (`!M M'. plane_map M /\ M' SUBSET M ==> plane_map M'`,
  REWRITE_TAC[plane_map] THEN MESON_TAC[PAIRWISE_MONO; SUBSET]);;

(* ------------------------------------------------------------------------- *)
(* The adjacency graph of a map.                                             *)
(* ------------------------------------------------------------------------- *)

let adjacency_graph = new_definition
 `adjacency_graph (M:(real^2->bool)->bool) =
  {{r1,r2} | adjacent_regions M r1 r2}`;;
