(* ========================================================================= *)
(* Quaternionic calculus.                                                    *)
(*                                                                           *)
(* Copyright (c) 2014 Marco Maggesi                                          *)
(* ========================================================================= *)

needs "Multivariate/complexes.ml";;

prioritize_real ();;

loadt "Quaternions/misc.hl";;        (* Miscellanea                         *)
loadt "Quaternions/quaternion.hl";;  (* Basic definitions about quaternions *)
loadt "Quaternions/qcalc.hl";;       (* Computing with literal quaternions  *)
loadt "Quaternions/qnormalizer.hl";; (* Normalization of quat. polynomials  *)
loadt "Quaternions/qanal.hl";;       (* Quaternionic analysis               *)
loadt "Quaternions/qderivative.hl";; (* Differential of quat. functions     *)
loadt "Quaternions/qisom.hl";;       (* Space isometries via quaternions    *)
