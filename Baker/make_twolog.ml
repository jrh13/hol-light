(* ========================================================================= *)
(* Partial loader for the two logarithms and the Steiner theorem: sections 1 *)
(* and 9 of Baker/make.ml; these use only the library-style file             *)
(* Baker/lemmas.ml and Library/ring_det.ml.                                  *)
(* ========================================================================= *)

needs "100/transcendence.ml";;
needs "Examples/mangoldt.ml";;

(* ------------------------------------------------------------------------- *)
(* 1. Library-style lemmas: generic lemmas shared by all sections. Needs     *)
(*    only the library.                                                      *)
(* ------------------------------------------------------------------------- *)

needs "Baker/lemmas.ml";;

(* ------------------------------------------------------------------------- *)
(* 9. Two logarithms: an explicit lower bound for linear forms in two        *)
(*    logarithms (interpolation determinants; the determinants are ring_det  *)
(*    of Library/ring_det.ml over complex_ring and real_ring,                *)
(*    COMPLEX_RING_DET, REAL_RING_DET), and the Steiner theorem on the       *)
(*    circuits of the 3x+1 problem. Needs only section 1                     *)
(*    (Baker/make_twolog.ml).                                                *)
(* ------------------------------------------------------------------------- *)

needs "Baker/twolog_det.ml";;
needs "Baker/twolog_interp.ml";;
needs "Baker/twolog_zero.ml";;
needs "Baker/twolog_core.ml";;
needs "Baker/twolog_param.ml";;
needs "Baker/twolog.ml";;
needs "Baker/steiner.ml";;
