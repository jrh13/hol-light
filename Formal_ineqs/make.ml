(* ========================================================================= *)
(* A tool for formal verification of nonlinear inequalities in HOL Light.    *)
(*                                                                           *)
(*                     (c) Alexey Solovyev 2012.                             *)
(*                                                                           *)
(*           Distributed under the same license as HOL Light.                *)
(* ========================================================================= *)

needs "Multivariate/realanalysis.ml";;

(* ------------------------------------------------------------------------- *)
(* Main load.                                                                *)
(* ------------------------------------------------------------------------- *)

load_path := (Filename.concat (!hol_dir) "Formal_ineqs") ::
             (!load_path);;

loadt "Formal_ineqs/verifier/m_verifier_main.hl";;

open M_verifier_main;;

(* ------------------------------------------------------------------------- *)
(* See docs/FormalVerifier.pdf for more information. A simple example:       *)
(*                                                                           *)
(* let ineq =                                                                *)
(*  `-- &1 / sqrt(&3) <= x /\ x <= sqrt(&2) /\ -- sqrt(pi) <= y /\ y <= &1   *)
(*   ==> x pow 2 * y - x * y pow 4 + y pow 6 - &7 + x pow 4 > -- #7.17995`;; *)
(* let th, stats = verify_ineq default_params 5 ineq;;                       *)
(*                                                                           *)
(* These files contain more substantial examples:                            *)
(*                                                                           *)
(* loadt "Formal_ineqs/examples.hl";;                                        *)
(* loadt "Formal_ineqs/examples_poly.hl";;                                   *)
(* loadt "Formal_ineqs/examples_flyspeck.hl";;                               *)
(* ------------------------------------------------------------------------- *)
