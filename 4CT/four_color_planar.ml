(* ========================================================================= *)
(* 4CT/four_color_planar.ml                                                  *)
(*                                                                           *)
(* The Four Colour Theorem for finite simple planar graphs in the sense of   *)
(* HOL Light's Autoformalization/planar_graph.ml, and its purely             *)
(* combinatorial forms for graphs without a Kuratowski obstruction (no       *)
(* subdivision of K5 or K3,3, by KURATOWSKI) or a Wagner obstruction (no K5  *)
(* or K3,3 minor, by WAGNER), all modulo the hypothesis reducibility         *)
(* discharged by the Part 2 computation                                      *)
(* (FOUR_COLOR_PLANAR_GRAPH_OF_REDUCIBILITY and the _KURATOWSKI_ and         *)
(* _WAGNER_ versions); make.ml derives the unconditional                     *)
(* FOUR_COLOR_PLANAR_GRAPH, FOUR_COLOR_KURATOWSKI and FOUR_COLOR_WAGNER by   *)
(* MP.                                                                       *)
(* ========================================================================= *)

needs "4CT/planar_graph_link.ml";;
needs "4CT/four_color.ml";;

let FOUR_COLOR_PLANAR_GRAPH_OF_REDUCIBILITY = prove
 (`reducibility
   ==> !V:A->bool E. planar_graph V E
                     ==> ?c:A->num. (!v. v IN V ==> c v < 4) /\
                                    (!u v. {u,v} IN E ==> ~(c u = c v))`,
  DISCH_THEN(MP_TAC o MATCH_MP
    (INST_TYPE [`:A#A`,`:A`] FOUR_COLOR_HYPERMAP)) THEN
  DISCH_THEN(MP_TAC o MATCH_MP FOUR_COLOR_PLANAR_GRAPH_OF_HYPERMAP) THEN
  REWRITE_TAC[proper_coloring]);;

let FOUR_COLOR_KURATOWSKI_OF_REDUCIBILITY = prove
 (`reducibility
   ==> !V:A->bool E.
         finite_simple_graph V E /\ ~graph_kuratowski_obstruction V E
         ==> ?c:A->num. (!v. v IN V ==> c v < 4) /\
                        (!u v. {u,v} IN E ==> ~(c u = c v))`,
  DISCH_THEN(MP_TAC o MATCH_MP FOUR_COLOR_PLANAR_GRAPH_OF_REDUCIBILITY) THEN
  MESON_TAC[KURATOWSKI]);;

let FOUR_COLOR_WAGNER_OF_REDUCIBILITY = prove
 (`reducibility
   ==> !V:A->bool E.
         finite_simple_graph V E /\ ~graph_wagner_obstruction V E
         ==> ?c:A->num. (!v. v IN V ==> c v < 4) /\
                        (!u v. {u,v} IN E ==> ~(c u = c v))`,
  DISCH_THEN(MP_TAC o MATCH_MP FOUR_COLOR_PLANAR_GRAPH_OF_REDUCIBILITY) THEN
  MESON_TAC[WAGNER]);;
