(* ========================================================================= *)
(* A tool for formal verification of nonlinear inequalities in HOL Light.    *)
(*                                                                           *)
(*                     (c) Alexey Solovyev 2012.                             *)
(*                                                                           *)
(*           Distributed under the same license as HOL Light.                *)
(* ========================================================================= *)

needs "Multivariate/realanalysis.ml";;

(* ------------------------------------------------------------------------- *)
(* For backwards compatibility, old versions of some sqrt theorems.          *)
(* In revision 182 (18th February 2014) these were strengthened to have      *)
(* fewer (or in some cases no) conditions. These _COMPAT versions ensure     *)
(* that the code will work correctly either with earlier or later HOL Light. *)
(* ------------------------------------------------------------------------- *)

let SQRT_MUL_COMPAT = prove
 (`!x y. &0 <= x /\ &0 <= y ==> sqrt(x * y) = sqrt x * sqrt y`,
  MESON_TAC[SQRT_MUL]);;

let SQRT_EQ_0_COMPAT = prove
 (`!x. &0 <= x ==> ((sqrt x = &0) <=> (x = &0))`,
  MESON_TAC[SQRT_EQ_0]);;

let SQRT_MONO_LT_COMPAT = prove
 (`!x y. &0 <= x /\ x < y ==> sqrt(x) < sqrt(y)`,
  MESON_TAC[SQRT_MONO_LT]);;

let SQRT_MONO_LE_COMPAT = prove
 (`!x y. &0 <= x /\ x <= y ==> sqrt(x) <= sqrt(y)`,
  MESON_TAC[SQRT_MONO_LE]);;

let SQRT_MONO_LT_EQ_COMPAT = prove
 (`!x y. &0 <= x /\ &0 <= y ==> (sqrt(x) < sqrt(y) <=> x < y)`,
  MESON_TAC[SQRT_MONO_LT_EQ]);;

let SQRT_MONO_LE_EQ_COMPAT = prove
 (`!x y. &0 <= x /\ &0 <= y ==> (sqrt(x) <= sqrt(y) <=> x <= y)`,
  MESON_TAC[SQRT_MONO_LE_EQ]);;

let SQRT_INJ_COMPAT = prove
 (`!x y. &0 <= x /\ &0 <= y ==> (sqrt(x) = sqrt(y) <=> x = y)`,
  MESON_TAC[SQRT_INJ]);;

let REAL_LE_LSQRT_COMPAT = prove
 (`!x y. &0 <= x /\ &0 <= y /\ x <= y pow 2 ==> sqrt(x) <= y`,
  MESON_TAC[REAL_LE_LSQRT]);;

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
