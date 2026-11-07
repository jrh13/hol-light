(* ========================================================================= *)
(* Partial loader for the Laurent bound for linear forms in two logarithms   *)
(* of rationals (Laurent 2008 at mu = 1): sections 1, 9 and 10 of            *)
(* Baker/make.ml. Section 10 uses only the library-style file                *)
(* Baker/lemmas.ml, Library/ring_det.ml and the two logarithm files of       *)
(* section 9 (not Baker/steiner.ml, which is loaded with section 9 for       *)
(* simplicity).                                                              *)
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

(* ------------------------------------------------------------------------- *)
(* 10. The Laurent bound for two logarithms of rationals (Laurent 2008 at    *)
(*     mu = 1): LAURENT_RATIONAL, LAURENT_RATIONAL_GENERAL,                  *)
(*     LAURENT_RATIONAL_PARAM. Needs only sections 1 and 9                   *)
(*     (Baker/make_laurent.ml).                                              *)
(* ------------------------------------------------------------------------- *)

needs "Baker/laurent_defs.ml";;
needs "Baker/laurent_det.ml";;
needs "Baker/laurent_binom.ml";;
needs "Baker/laurent_glemma.ml";;
needs "Baker/laurent_interp.ml";;
needs "Baker/laurent_core.ml";;
needs "Baker/laurent_param_main.ml";;
needs "Baker/laurent_param.ml";;
needs "Baker/laurent_corner.ml";;
needs "Baker/laurent.ml";;
