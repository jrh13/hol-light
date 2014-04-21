(* ========================================================================= *)
(* Irrationality of sqrt(2) and more general results.                        *)
(* ========================================================================= *)

needs "Library/prime.ml";;              (* For number-theoretic lemmas       *)
needs "Library/floor.ml";;              (* For definition of rationals       *)
needs "Multivariate/vectors.ml";;       (* For square roots                  *)

(* ------------------------------------------------------------------------- *)
(* Most general irrationality of square root result.                         *)
(* ------------------------------------------------------------------------- *)

let IRRATIONAL_SQRT_NONSQUARE = prove
 (`!n. rational(sqrt(&n)) ==> ?m. n = m EXP 2`,
  REWRITE_TAC[rational] THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o AP_TERM `\x:real. x pow 2`) THEN
  SIMP_TAC[SQRT_POW_2; REAL_POS] THEN
  ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [integer])) THEN
  ASM_REWRITE_TAC[REAL_ABS_DIV] THEN DISCH_THEN(MP_TAC o MATCH_MP(REAL_FIELD
   `p = (n / m) pow 2 ==> ~(m = &0) ==> m pow 2 * p = n pow 2`)) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[REAL_ABS_ZERO]; ALL_TAC] THEN
  REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_MUL; REAL_OF_NUM_EQ] THEN
  ASM_MESON_TAC[EXP_MULT_EXISTS; REAL_ABS_ZERO; REAL_OF_NUM_EQ]);;

(* ------------------------------------------------------------------------- *)
(* In particular, prime numbers.                                             *)
(* ------------------------------------------------------------------------- *)

let IRRATIONAL_SQRT_PRIME = prove
 (`!p. prime p ==> ~rational(sqrt(&p))`,
  GEN_TAC THEN ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN REWRITE_TAC[] THEN
  DISCH_THEN(CHOOSE_THEN SUBST1_TAC o MATCH_MP IRRATIONAL_SQRT_NONSQUARE) THEN
  REWRITE_TAC[PRIME_EXP; ARITH_EQ]);;

(* ------------------------------------------------------------------------- *)
(* In particular, sqrt(2) is irrational.                                     *)
(* ------------------------------------------------------------------------- *)

let IRRATIONAL_SQRT_2 = prove
 (`~rational(sqrt(&2))`,
  SIMP_TAC[IRRATIONAL_SQRT_PRIME; PRIME_2]);;
