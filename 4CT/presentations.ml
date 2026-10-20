(* ========================================================================= *)
(* 4CT/presentations.ml                                                      *)
(*                                                                           *)
(* present5.v to present11.v: the seven presentation lemmas exclude5, ...,   *)
(* exclude11 stating excluded_arity (:A) n for the hub sizes n = 5..11,      *)
(* proved by running Gonthier's scripts (presentations_data.ml, 14421 steps) *)
(* through the interpreter of present_eval.ml; every Reducible, Hubcap,      *)
(* Similar and Pcase side condition is evaluated by call-by-value reduction. *)
(* ========================================================================= *)

needs "4CT/present_eval.ml";;

step_report := 500;;

let exclude5 = prove_exclude 5 present5_steps;;
let exclude6 = prove_exclude 6 present6_steps;;
let exclude7 = prove_exclude 7 present7_steps;;
let exclude8 = prove_exclude 8 present8_steps;;
let exclude9 = prove_exclude 9 present9_steps;;
let exclude10 = prove_exclude 10 present10_steps;;
let exclude11 = prove_exclude 11 present11_steps;;

