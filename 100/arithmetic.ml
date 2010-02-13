(* ========================================================================= *)
(* Sum of an arithmetic series.                                              *)
(* ========================================================================= *)

let ARITHMETIC_PROGRESSION_LEMMA = prove
 (`!n. nsum(0..n) (\i. a + d * i) = ((n + 1) * (2 * a + n * d)) DIV 2`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[NSUM_CLAUSES_NUMSEG] THEN ARITH_TAC);;

let ARITHMETIC_PROGRESSION = prove
 (`!n. 1 <= n 
       ==> nsum(0..n-1) (\i. a + d * i) = (n * (2 * a + (n - 1) * d)) DIV 2`,
  INDUCT_TAC THEN REWRITE_TAC[ARITHMETIC_PROGRESSION_LEMMA; SUC_SUB1] THEN
  ARITH_TAC);;
