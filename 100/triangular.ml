(* ========================================================================= *)
(* Sum of reciprocals of triangular numbers.                                 *)
(* ========================================================================= *)

needs "Multivariate/misc.ml";;  (*** Just for REAL_ARCH_INV! ***)

prioritize_real();;

(* ------------------------------------------------------------------------- *)
(* Definition of triangular numbers.                                         *)
(* ------------------------------------------------------------------------- *)

let triangle = new_definition
 `triangle n = (n * (n + 1)) DIV 2`;;

(* ------------------------------------------------------------------------- *)
(* Mapping them into the reals: division is exact.                           *)
(* ------------------------------------------------------------------------- *)

let REAL_TRIANGLE = prove
 (`&(triangle n) = (&n * (&n + &1)) / &2`,
  MATCH_MP_TAC(REAL_ARITH `&2 * x = y ==> x = y / &2`) THEN
  REWRITE_TAC[triangle; REAL_OF_NUM_MUL; REAL_OF_NUM_ADD; REAL_OF_NUM_EQ] THEN
  SUBGOAL_THEN `EVEN(n * (n + 1))` MP_TAC THENL
   [REWRITE_TAC[EVEN_MULT; EVEN_ADD; ARITH] THEN CONV_TAC TAUT;
    REWRITE_TAC[EVEN_EXISTS] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    AP_TERM_TAC THEN MATCH_MP_TAC DIV_MULT THEN REWRITE_TAC[ARITH]]);;

(* ------------------------------------------------------------------------- *)
(* Sum of a finite number of terms.                                          *)
(* ------------------------------------------------------------------------- *)

let TRIANGLE_FINITE_SUM = prove
 (`!n. sum(1..n) (\k. &1 / &(triangle k)) = &2 - &2 / (&n + &1)`,
  INDUCT_TAC THEN
  ASM_REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH_EQ; ARITH_RULE `1 <= SUC n`] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[REAL_TRIANGLE; GSYM REAL_OF_NUM_SUC] THEN CONV_TAC REAL_FIELD);;

(* ------------------------------------------------------------------------- *)
(* Hence limit.                                                              *)
(* ------------------------------------------------------------------------- *)

let TRIANGLE_CONVERGES = prove
 (`!e. &0 < e
       ==> ?N. !n. n >= N
                   ==> abs(sum(1..n) (\k. &1 / &(triangle k)) - &2) < e`,
  GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [REAL_ARCH_INV] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `2 * N + 1` THEN REWRITE_TAC[GE] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[TRIANGLE_FINITE_SUM; REAL_ARITH `abs(x - y - x) = abs y`] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `inv(&N)` THEN
  ASM_SIMP_TAC[REAL_ABS_DIV; REAL_ABS_NUM] THEN
  ONCE_REWRITE_TAC[GSYM REAL_INV_DIV] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
  SIMP_TAC[REAL_LE_RDIV_EQ; REAL_OF_NUM_LT; ARITH] THEN
  REWRITE_TAC[REAL_ARITH `abs(&n + &1) = &n + &1`] THEN
  REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_MUL; REAL_OF_NUM_LE] THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* In terms of limits.                                                       *)
(* ------------------------------------------------------------------------- *)

needs "Library/analysis.ml";;

override_interface ("-->",`(tends_num_real)`);;

let TRIANGLE_CONVERGES' = prove
 (`(\n. sum(1..n) (\k. &1 / &(triangle k))) --> &2`,
  REWRITE_TAC[SEQ; TRIANGLE_CONVERGES]);;
