(* ========================================================================= *)
(* 4CT/four_color_map.ml                                                     *)
(*                                                                           *)
(* The Four Colour Theorem for maps of regions in the plane modulo           *)
(* reducibility, FOUR_COLOR_MAP_OF_REDUCIBILITY : |- reducibility ==> !M.    *)
(* plane_map M ==> map_colorable 4 M (Gonthier's four_color in fourcolor.v), *)
(* and its unfolded form FOUR_COLOR_MAP_EXPLICIT_OF_REDUCIBILITY, assembled  *)
(* from the planar-graph form (four_color_planar.ml) and the map theorem     *)
(* modulo the planar-graph theorem (map_main.ml).  make.ml derives the       *)
(* unconditional FOUR_COLOR_MAP and FOUR_COLOR_MAP_EXPLICIT by MP once Part  *)
(* 2 has proved reducibility.                                                *)
(* ========================================================================= *)

needs "4CT/four_color_planar.ml";;
needs "4CT/map_main.ml";;

let FOUR_COLOR_MAP_OF_REDUCIBILITY = prove
 (`reducibility ==> !M. plane_map M ==> map_colorable 4 M`,
  DISCH_THEN(MP_TAC o MATCH_MP
    (INST_TYPE [`:real^2->bool`,`:A`]
      FOUR_COLOR_PLANAR_GRAPH_OF_REDUCIBILITY)) THEN
  REWRITE_TAC[GSYM planar_graphs_four_colorable] THEN
  DISCH_THEN(ACCEPT_TAC o MATCH_MP FOUR_COLOR_MAP_OF_PLANAR_GRAPHS));;

(* The same with plane_map and map_colorable unfolded                        *)

let FOUR_COLOR_MAP_EXPLICIT_OF_REDUCIBILITY = prove
 (`reducibility
   ==> !M:(real^2->bool)->bool.
        (!r. r IN M ==> open r /\ connected r) /\ pairwise DISJOINT M
        ==> ?c:(real^2->bool)->num.
              (!r. r IN M ==> c r < 4) /\
              (!r1 r2. r1 IN M /\ r2 IN M /\ ~(r1 = r2) /\
                       (?z. z IN closure r1 INTER closure r2 /\
                            (!r. r IN M /\ z IN closure r ==>
                            r = r1 \/ r = r2))
                       ==> ~(c r1 = c r2))`,
  DISCH_THEN(MP_TAC o MATCH_MP FOUR_COLOR_MAP_OF_REDUCIBILITY) THEN
  REWRITE_TAC[plane_map; map_colorable; adjacent_regions]);;
