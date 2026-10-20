(* ========================================================================= *)
(* 4CT/make.ml                                                               *)
(*                                                                           *)
(* The Four Colour Theorem in HOL Light, end to end.                         *)
(*                                                                           *)
(* With the directory containing 4CT on the load path (HOL Light's default   *)
(* load_path is ["."; "$"]: install 4CT under the HOL Light root, beside     *)
(* Autoformalization/ and eval_compile/, or start HOL Light from a directory *)
(* containing all three)                                                     *)
(* and an unlimited stack (ulimit -s unlimited),                             *)
(*                                                                           *)
(*   loadt "4CT/make.ml";;                                                   *)
(*                                                                           *)
(* loads Multivariate with Autoformalization/planar_graph.ml, the whole      *)
(* development and the reducibility computation, and leaves the theorem for  *)
(* hypermaps, planar graphs and plane maps,                                  *)
(*                                                                           *)
(*   FOUR_COLOR : |- !H:(A)hypermap. planar_hypermap H /\ bridgeless H       *)
(*                   ==> four_colorable H                                    *)
(*                                                                           *)
(*   FOUR_COLOR_PLANAR_GRAPH :                                               *)
(*     |- !V E. planar_graph V E                                             *)
(*              ==> ?c. (!v. v IN V ==> c v < 4) /\                          *)
(*                      (!u v. {u,v} IN E ==> ~(c u = c v))                  *)
(*                                                                           *)
(*   FOUR_COLOR_MAP : |- !M. plane_map M ==> map_colorable 4 M               *)
(*                                                                           *)
(* with no hypotheses and nothing beyond HOL Light's kernel and definitions  *)
(* (no new axioms, no CHEAT_TAC, no mk_thm in any loaded file).  The         *)
(* development follows Gonthier's Coq proof (fourcolor/theories/proof/);     *)
(* FOUR_COLOR is his four_color_hypermap.  FOUR_COLOR_PLANAR_GRAPH is for    *)
(* finite simple planar graphs in the sense of planar_graph.ml, via the      *)
(* hypermap of a graph; FOUR_COLOR_KURATOWSKI and FOUR_COLOR_WAGNER give the *)
(* same conclusion for finite simple graphs with no subdivision, or no       *)
(* minor, of K5 or K3,3.  FOUR_COLOR_MAP (Gonthier's four_color) is for maps *)
(* of regions in the plane: every set of pairwise disjoint open connected    *)
(* subsets of real^2, finite or not, has a colouring with four colours in    *)
(* which two regions sharing a border point (a point of both closures lying  *)
(* in the closure of no third region) get different colours;                 *)
(* FOUR_COLOR_MAP_EXPLICIT is the same with plane_map and map_colorable      *)
(* unfolded.  It comes from the planar-graph form: the adjacency graph of a  *)
(* finite map is a minor of a grid graph; infinite maps by compactness.      *)
(*                                                                           *)
(* planar_graph.ml (with Multivariate) is loaded first.                      *)
(*                                                                           *)
(* PART 1 -- the mathematics (sections A-G, P and M; every theory file also  *)
(* loads its own prerequisites, so each can be loaded on its own):           *)
(*   A  foundation      general (lemmas about lists, iteration, orbits and   *)
(*                      finite sets), hypermap, geometry, color, coloring,   *)
(*                      walkup, jordan, chromogram, kempe                    *)
(*   B  surgery         patch, snip, preembedding, revsnip, embed_prelim,    *)
(*                      cfmap (configuration maps from programs), sew,       *)
(*                      revsnip_tail                                         *)
(*   C  trees           dyck, ctree, gtree, cfcolor, initctree, initgtree,   *)
(*                      ctreerestrict, gtreerestrict, kempetree,             *)
(*                      cpcolor_correct                                      *)
(*   D  Birkhoff etc.   birkhoff (the Birkhoff checks by computation),       *)
(*                      embed (the embedding of a configuration in a         *)
(*                      minimal counter-example), contract, EMBED_CONTRACT   *)
(*   E  reducibility    cfcontract, kempetree_wrap, cfreducible              *)
(*                      (check_reducible cf ==> cfreducible cf, with the     *)
(*                      triad consequence)                                   *)
(*   F  configurations  part, part_mirror, quiz, cube (cubification),        *)
(*                      configurations (the 633 configurations)              *)
(*   G  unavoidability  part_converse, discharge, hubcap, cfquiz, quiztree,  *)
(*                      redpart, present, the computations quiztree_eval,    *)
(*                      redpart_eval, presentations (= present5..11.v),      *)
(*                      unavoidability, and four_color with                  *)
(*        FOUR_COLOR_HYPERMAP : |- reducibility ==>                          *)
(*               !H. planar_hypermap H /\ bridgeless H ==> four_colorable H  *)
(*        reducibility = !cf. MEM cf the_configs ==> check_reducible cf      *)
(*   P  planar graphs   planar_graph_link (the hypermap of a graph),         *)
(*                      four_color_planar (the graph forms modulo            *)
(*                      reducibility)                                        *)
(*   M  plane maps      map_defs (the notions), map_grid (the adjacency      *)
(*                      graph of a finite map is a minor of a grid graph,    *)
(*                      hence planar), map_main (finite maps; compactness,   *)
(*                      via Tychonoff, for infinite maps), four_color_map    *)
(*                      (the map forms modulo reducibility)                  *)
(*                                                                           *)
(* PART 2 -- the computation (section H): |- check_reducible cfNNN <=> T     *)
(* for each of the 633 configurations, by proof-producing evaluation         *)
(* (Solovyev's eval_compile, in eval_compile/ beside 4CT/, MIT licence:     *)
(* one small inference per rewrite step, compiled OCaml control flow) of     *)
(* the definitions through evaluation-friendly reformulations, each proved   *)
(* equal to the original definition:                                         *)
(*   part2_eval.ml      computable, first-order, step-reduced and            *)
(*                      clause-fused forms of the definitions, and the       *)
(*                      rule databases                                       *)
(*   part2_compiled.hl  the evaluator generated from the final rule set      *)
(*                      (regenerate with part2_compile.ml, bytecode only)    *)
(*   part2_run.ml       p2_run_indices, which runs it over configurations    *)
(*   part2_final.ml     runs it over all of them (FOURCOLOR_CONFIGS=lo-hi    *)
(*                      restricts the range, for testing), then REDUCIBILITY *)
(*                      by rewriting with the 633 results and FOUR_COLOR =   *)
(*                      MP FOUR_COLOR_HYPERMAP REDUCIBILITY; loaded on its   *)
(*                      own it proves just FOUR_COLOR, without Multivariate  *)
(*                      (make native-hypermap)                               *)
(* and finally every form of the theorem by MP with REDUCIBILITY.            *)
(*                                                                           *)
(* COST (sequential, native, one core of a 2 x 96-core Graviton4;            *)
(* EFFICIENCY_NOTES.md has more): Part 1 ~2 h 10 min (of which ~1 h 50 min   *)
(* are the unavoidability computations), Part 2 ~8 h 45 min; ~1 GB RAM.      *)
(* Compiling the native binary takes ~2.5 h and ~50 GB, since Multivariate   *)
(* is inlined.  In the bytecode toplevel the run takes about two days.       *)
(* FOURCOLOR_CONFIGS=lo-hi in the environment restricts Part 2 to a          *)
(* sub-range (for testing: everything else is loaded, and the final assembly *)
(* then fails on purpose).                                                   *)
(*                                                                           *)
(* PARALLEL (OCaml 5 or later): make_parallel.ml loads parallel.ml and then  *)
(* this file, which then evaluates the side conditions of the presentation   *)
(* scripts and the 633 configurations in parallel (par_hook.ml; same files,  *)
(* same theorems): natively about 22 min on 128 cores, with ~48 GB.  The     *)
(* Makefile chooses it automatically when OCaml is 5 or later.               *)
(* ========================================================================= *)

needs "Library/iter.ml";;
needs "Library/permutations.ml";;

(* ------------------------------------------------------------------------- *)
(* Multivariate and Autoformalization/planar_graph.ml (for sections P, M).   *)
(* ------------------------------------------------------------------------- *)

needs "Autoformalization/planar_graph.ml";;

prioritize_num();;

parse_as_infix("::",(23,"right"));;
override_interface("::",`CONS`);;

(* ------------------------------------------------------------------------- *)
(* A. Foundation: hypermaps, geometry, colourings, walkup, Jordan,           *)
(* chromograms, Kempe chains                                                 *)
(* ------------------------------------------------------------------------- *)

needs "4CT/general.ml";;
needs "4CT/hypermap.ml";;
needs "4CT/geometry.ml";;
needs "4CT/color.ml";;
needs "4CT/coloring.ml";;
needs "4CT/walkup.ml";;
needs "4CT/jordan.ml";;
needs "4CT/chromogram.ml";;
needs "4CT/kempe.ml";;

let _ = Gc.compact();;

(* ------------------------------------------------------------------------- *)
(* B. Surgery: patch, snip, pre-embeddings, revsnip, embedding               *)
(* preliminaries, configuration maps, sew                                    *)
(* ------------------------------------------------------------------------- *)

needs "4CT/patch.ml";;
needs "4CT/snip.ml";;
needs "4CT/preembedding.ml";;
needs "4CT/revsnip.ml";;
needs "4CT/embed_prelim.ml";;
needs "4CT/cfmap.ml";;
needs "4CT/sew.ml";;
needs "4CT/revsnip_tail.ml";;

let _ = Gc.compact();;

(* ------------------------------------------------------------------------- *)
(* C. Colouring trees and the Kempe-closure tree                             *)
(* ------------------------------------------------------------------------- *)

needs "4CT/dyck.ml";;
needs "4CT/ctree.ml";;
needs "4CT/gtree.ml";;
needs "4CT/cfcolor.ml";;
needs "4CT/initctree.ml";;
needs "4CT/initgtree.ml";;
needs "4CT/ctreerestrict.ml";;
needs "4CT/gtreerestrict.ml";;
needs "4CT/kempetree.ml";;
needs "4CT/cpcolor_correct.ml";;

let _ = Gc.compact();;

(* ------------------------------------------------------------------------- *)
(* D. Birkhoff, the embedding morphism, contracts                            *)
(* ------------------------------------------------------------------------- *)

needs "4CT/birkhoff.ml";;
needs "4CT/embed.ml";;
needs "4CT/contract.ml";;
needs "4CT/embed_contract.ml";;

let _ = Gc.compact();;

(* ------------------------------------------------------------------------- *)
(* E. Configuration contracts and the bridge check_reducible ==> cfreducible *)
(*                                         (with the triad consequence)      *)
(* ------------------------------------------------------------------------- *)

needs "4CT/cfcontract.ml";;
needs "4CT/kempetree_wrap.ml";;
needs "4CT/cfreducible.ml";;

let _ = Gc.compact();;

(* ------------------------------------------------------------------------- *)
(* F. Parts, quizzes, cubification, the 633 configurations                   *)
(* ------------------------------------------------------------------------- *)

needs "4CT/part.ml";;
needs "4CT/part_mirror.ml";;
needs "4CT/quiz.ml";;
needs "4CT/cube.ml";;
needs "4CT/configurations.ml";;

let _ = Gc.compact();;

(* ------------------------------------------------------------------------- *)
(* G. Unavoidability: discharging, hubcaps, quiz trees, the presentation     *)
(* scripts; the hypermap theorem                                             *)
(* ------------------------------------------------------------------------- *)

needs "4CT/part_converse.ml";;
needs "4CT/discharge.ml";;
needs "4CT/hubcap.ml";;
needs "4CT/cfquiz.ml";;
needs "4CT/quiztree.ml";;
needs "4CT/redpart.ml";;
needs "4CT/present.ml";;
needs "4CT/quiztree_eval.ml";;
needs "4CT/redpart_eval.ml";;
needs "4CT/presentations.ml";;
needs "4CT/unavoidability.ml";;
needs "4CT/four_color.ml";;

let _ = Gc.compact();;

(* ------------------------------------------------------------------------- *)
(* P. Planar graphs: the hypermap of a graph and the graph forms             *)
(* ------------------------------------------------------------------------- *)

needs "4CT/planar_graph_link.ml";;
needs "4CT/four_color_planar.ml";;

(* ------------------------------------------------------------------------- *)
(* M. Plane maps: the adjacency graph, finite maps, compactness              *)
(* ------------------------------------------------------------------------- *)

needs "4CT/map_defs.ml";;
needs "4CT/map_grid.ml";;
needs "4CT/map_main.ml";;
needs "4CT/four_color_map.ml";;

let _ = Gc.compact();;
Printf.printf "=== 4CT/make.ml: Part 1 (the mathematics) loaded ===\n%!";;

(* ------------------------------------------------------------------------- *)
(* H. Part 2: the reducibility computation and the theorem.                  *)
(* ------------------------------------------------------------------------- *)

needs "4CT/part2_eval.ml";;
needs "4CT/part2_compiled.hl";;
needs "4CT/part2_run.ml";;
needs "4CT/part2_final.ml";;

(* ------------------------------------------------------------------------- *)
(* The theorem in all its forms.                                             *)
(* ------------------------------------------------------------------------- *)

let REDUCIBILITY, FOUR_COLOR = p2_final();;

let FOUR_COLOR_PLANAR_GRAPH =
  MP FOUR_COLOR_PLANAR_GRAPH_OF_REDUCIBILITY REDUCIBILITY;;
let FOUR_COLOR_KURATOWSKI =
  MP FOUR_COLOR_KURATOWSKI_OF_REDUCIBILITY REDUCIBILITY;;
let FOUR_COLOR_WAGNER = MP FOUR_COLOR_WAGNER_OF_REDUCIBILITY REDUCIBILITY;;
let FOUR_COLOR_MAP = MP FOUR_COLOR_MAP_OF_REDUCIBILITY REDUCIBILITY;;
let FOUR_COLOR_MAP_EXPLICIT =
  MP FOUR_COLOR_MAP_EXPLICIT_OF_REDUCIBILITY REDUCIBILITY;;

do_list
 (fun (name,th) ->
    Printf.printf "=== 4CT/make.ml: %s = %s (hyps %d) ===\n%!"
      name (string_of_thm th) (length(hyp th)))
 ["FOUR_COLOR",FOUR_COLOR; "FOUR_COLOR_PLANAR_GRAPH",FOUR_COLOR_PLANAR_GRAPH;
  "FOUR_COLOR_KURATOWSKI",FOUR_COLOR_KURATOWSKI;
  "FOUR_COLOR_WAGNER",FOUR_COLOR_WAGNER; "FOUR_COLOR_MAP",FOUR_COLOR_MAP;
  "FOUR_COLOR_MAP_EXPLICIT",FOUR_COLOR_MAP_EXPLICIT];;
