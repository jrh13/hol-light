let fib = define
 `fib n = if n = 0 \/ n = 1 then 1 else fib(n - 1) + fib(n - 2)`;;

let fib2 = define
 `(fib2 0 = 1) /\
  (fib2 1 = 1) /\
  (fib2 (n + 2) = fib2(n) + fib2(n + 1))`;;

let halve = define `halve (2 * n) = n`;;

let unknown = define `unknown n = unknown(n + 1)`;;

define
 `!n. collatz(n) = if n <= 1 then n
                   else if EVEN(n) then collatz(n DIV 2)
                   else collatz(3 * n + 1)`;;

let fusc_def = define
 `(fusc (2 * n) = if n = 0 then 0 else fusc(n)) /\
  (fusc (2 * n + 1) = if n = 0 then 1 else fusc(n) + fusc(n + 1))`;;

let fusc = prove
 (`fusc 0 = 0 /\
   fusc 1 = 1 /\
   fusc (2 * n) = fusc(n) /\
   fusc (2 * n + 1) = fusc(n) + fusc(n + 1)`,
  REWRITE_TAC[fusc_def] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(INST [`0`,`n:num`] fusc_def) THEN ARITH_TAC);;

let binom = define
 `(!n. binom(n,0) = 1) /\
  (!k. binom(0,SUC(k)) = 0) /\
  (!n k. binom(SUC(n),SUC(k)) = binom(n,SUC(k)) + binom(n,k))`;;

let BINOM_LT = prove
 (`!n k. n < k ==> (binom(n,k) = 0)`,
  INDUCT_TAC THEN INDUCT_TAC THEN REWRITE_TAC[binom; ARITH; LT_SUC; LT] THEN
  ASM_SIMP_TAC[ARITH_RULE `n < k ==> n < SUC(k)`; ARITH]);;

let BINOM_REFL = prove
 (`!n. binom(n,n) = 1`,
  INDUCT_TAC THEN ASM_SIMP_TAC[binom; BINOM_LT; LT; ARITH]);;

let BINOM_FACT = prove
 (`!n k. FACT n * FACT k * binom(n+k,k) = FACT(n + k)`,
  INDUCT_TAC THEN REWRITE_TAC[FACT; ADD_CLAUSES; MULT_CLAUSES; BINOM_REFL] THEN
  INDUCT_TAC THEN REWRITE_TAC[ADD_CLAUSES; FACT; MULT_CLAUSES; binom] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `SUC k`) THEN POP_ASSUM MP_TAC THEN
  REWRITE_TAC[ADD_CLAUSES; FACT; binom] THEN CONV_TAC NUM_RING);;

let BINOMIAL_THEOREM = prove
 (`!n. (x + y) EXP n = nsum(0..n) (\k. binom(n,k) * x EXP k * y EXP (n - k))`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[EXP] THEN
  REWRITE_TAC[NSUM_SING_NUMSEG; binom; SUB_REFL; EXP; MULT_CLAUSES] THEN
  SIMP_TAC[NSUM_CLAUSES_LEFT; ADD1; ARITH_RULE `0 <= n + 1`; NSUM_OFFSET] THEN
  ASM_REWRITE_TAC[EXP; binom; GSYM ADD1; GSYM NSUM_LMUL] THEN
  REWRITE_TAC[RIGHT_ADD_DISTRIB; NSUM_ADD_NUMSEG; MULT_CLAUSES; SUB_0] THEN
  MATCH_MP_TAC(ARITH_RULE `a = e /\ b = c + d ==> a + b = c + d + e`) THEN
  CONJ_TAC THENL [REWRITE_TAC[MULT_AC; SUB_SUC]; REWRITE_TAC[GSYM EXP]] THEN
  SIMP_TAC[ADD1; SYM(REWRITE_CONV[NSUM_OFFSET]`nsum(m+1..n+1) (\i. f i)`)] THEN
  REWRITE_TAC[NSUM_CLAUSES_NUMSEG; GSYM ADD1; LE_SUC; LE_0] THEN
  SIMP_TAC[NSUM_CLAUSES_LEFT; LE_0] THEN
  SIMP_TAC[BINOM_LT; LT; MULT_CLAUSES; ADD_CLAUSES; SUB_0; EXP; binom] THEN
  SIMP_TAC[ARITH; ARITH_RULE `k <= n ==> SUC n - k = SUC(n - k)`; EXP] THEN
  REWRITE_TAC[MULT_AC]);;
