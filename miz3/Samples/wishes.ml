let EXAMPLE = prove
 (`!n. nsum(0..n) (\i. i) = (n*(n + 1)) DIV 2`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[NSUM_CLAUSES_NUMSEG] THEN ARITH_TAC);;

let EXAMPLE_IN_MIZAR_LIGHT = thm `;
  !n. nsum (0..n) (\i. i) = (n * (n + 1)) DIV 2 [1]
  proof
    nsum (0..0) (\i. i) = 0 [2] by NSUM_CLAUSES_NUMSEG;
      ... = (0 * (0 + 1)) DIV 2 [3] by ARITH_TAC;
    !n. nsum (0..n) (\i. i) = (n * (n + 1)) DIV 2
        ==> nsum (0..SUC n) (\i. i) = (SUC n * (SUC n + 1)) DIV 2 [4]
    proof
      let n be num;
      assume nsum (0..n) (\i. i) = (n * (n + 1)) DIV 2 [5];
    qed by #;
  qed by INDUCT_TAC from 3,4`;;
