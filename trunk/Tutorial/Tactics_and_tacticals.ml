g `2 <= n /\ n <= 2 ==> f(2,2) + n < f(n,n) + 7`;;
e DISCH_TAC;;
b();;
e(CONV_TAC(REWRITE_CONV[LE_ANTISYM]));;
e(SIMP_TAC[]);;
e(ONCE_REWRITE_TAC[EQ_SYM_EQ]);;
e DISCH_TAC;;
e(ASM_REWRITE_TAC[]);;
e(CONV_TAC ARITH_RULE);;
let trivial = top_thm();;

g `2 <= n /\ n <= 2 ==> f(2,2) + n < f(n,n) + 7`;;
e(CONV_TAC(REWRITE_CONV[LE_ANTISYM]));;
e(SIMP_TAC[]);;
e(ONCE_REWRITE_TAC[EQ_SYM_EQ]);;
e DISCH_TAC;;
e(ASM_REWRITE_TAC[]);;
e(CONV_TAC ARITH_RULE);;
let trivial = top_thm();;

g `2 <= n /\ n <= 2 ==> f(2,2) + n < f(n,n) + 7`;;
e(CONV_TAC(REWRITE_CONV[LE_ANTISYM]) THEN
  SIMP_TAC[] THEN ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC ARITH_RULE);;
let trivial = top_thm();;

let trivial = prove
 (`2 <= n /\ n <= 2 ==> f(2,2) + n < f(n,n) + 7`,
  CONV_TAC(REWRITE_CONV[LE_ANTISYM]) THEN
  SIMP_TAC[] THEN ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC ARITH_RULE);;

let trivial = prove
 (`!x y:real. &0 < x * y ==> (&0 < x <=> &0 < y)`,
  REPEAT GEN_TAC THEN MP_TAC(SPECL [`--x`; `y:real`] REAL_LE_MUL) THEN
  MP_TAC(SPECL [`x:real`; `--y`] REAL_LE_MUL) THEN REAL_ARITH_TAC);;

let trivial = prove
 (`!x y:real. &0 < x * y ==> (&0 < x <=> &0 < y)`,
  MATCH_MP_TAC REAL_WLOG_LE THEN CONJ_TAC THEN REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`--x`; `y:real`] REAL_LE_MUL) THEN REAL_ARITH_TAC);;

let SUM_OF_NUMBERS = prove
 (`!n. nsum(1..n) (\i. i) = (n * (n + 1)) DIV 2`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[NSUM_CLAUSES_NUMSEG] THEN ARITH_TAC);;

let SUM_OF_SQUARES = prove
 (`!n. nsum(1..n) (\i. i * i) = (n * (n + 1) * (2 * n + 1)) DIV 6`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[NSUM_CLAUSES_NUMSEG] THEN ARITH_TAC);;

let SUM_OF_CUBES = prove
 (`!n. nsum(1..n) (\i. i*i*i) = (n * n * (n + 1) * (n + 1)) DIV 4`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[NSUM_CLAUSES_NUMSEG] THEN ARITH_TAC);;
