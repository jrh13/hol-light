(* ========================================================================= *)
(*                          The Jordan Curve Theorem                         *)
(*                                                                           *)
(*                             Proof by Tom Hales                            *)
(*                                                                           *)
(*           A few tweaks by John Harrison for the latest HOL Light          *)
(* ========================================================================= *)

(*** Standard HOL Light library ***)

loads "Library/analysis.ml";;
loads "Library/transc.ml";;
loads "Examples/polylog.ml";;

(*** New stuff ***)

loadt "Jordan/tactics_refine.ml";;
loadt "Jordan/lib_ext.ml";;
loadt "Jordan/tactics_fix.ml";;
loadt "Jordan/parse_ext_override_interface.ml";;
loadt "Jordan/tactics_ext.ml";;
loadt "Jordan/num_ext_gcd.ml";;
loadt "Jordan/num_ext_nabs.ml";;
loadt "Jordan/real_ext_geom_series.ml";;
loadt "Rqe/num_calc_simp.ml";;
loadt "Jordan/real_ext.ml";;
loadt "Jordan/float.ml";;
loadt "Jordan/tactics_ext2.ml";;
loadt "Jordan/misc_defs_and_lemmas.ml";;
loadt "Jordan/metric_spaces.ml";;
loadt "Jordan/jordan_curve_theorem.ml";;
