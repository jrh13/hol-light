let ARITHMETIC_PROGRESSION_SIMPLE = prove
 (`!n. nsum(1..n) (\i. i) = (n*(n + 1)) DIV 2`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[NSUM_CLAUSES_NUMSEG] THEN
  ARITH_TAC);;

horizon := 1;;

thm `;
!n. nsum(0..n) (\i. i) = (n*(n + 1)) DIV 2
proof
  nsum(0..0) (\i. i) = 0 by NSUM_CLAUSES_NUMSEG;
    .= (0*(0 + 1)) DIV 2 [A1] by ARITH_TAC;
  now let n be num;
    assume nsum(0..n) (\i. i) = (n*(n + 1)) DIV 2;
    nsum(0..SUC n) (\i. i) = (n*(n + 1)) DIV 2 + SUC n
      by NSUM_CLAUSES_NUMSEG,ARITH_RULE (parse_term "0 <= SUC n");
    thus .= ((SUC n)*(SUC n + 1)) DIV 2 by ARITH_TAC;
  end;
qed by INDUCT_TAC,A1`;;

thm `;
now
  (if 1 = 0 then 0 else 0) = (0 * (0 + 1)) DIV 2 [A1] by ARITH_TAC;
  nsum (1..0) (\i. i) = (0 * (0 + 1)) DIV 2 [A2]
    by REWRITE_TAC,NSUM_CLAUSES_NUMSEG,A1;
  now [A3]
    let n be num;
    assume nsum (1..n) (\i. i) = (n * (n + 1)) DIV 2 [A4];
    (if 1 <= SUC n then (n * (n + 1)) DIV 2 + SUC n else (n * (n + 1)) DIV 2) =
      (SUC n * (SUC n + 1)) DIV 2 [A5] by ARITH_TAC;
    thus nsum (1..SUC n) (\i. i) = (SUC n * (SUC n + 1)) DIV 2 [A6]
      by REWRITE_TAC,NSUM_CLAUSES_NUMSEG,A4,A5;
  end;
  thus !n. nsum (1..n) (\i. i) = (n * (n + 1)) DIV 2 [A7] by INDUCT_TAC,A2,A3;
end`;;

let EXAMPLE = ref None;;

EXAMPLE := Some `;
!n. nsum(0..n) (\i. i) = (n*(n + 1)) DIV 2
proof
  nsum(0..0) (\i. i) = (0*(0 + 1)) DIV 2;
  now let n be nat;
    assume nsum(0..n) (\i. i) = (n*(n + 1)) DIV 2;
    thus nsum(0..SUC n) (\i. i) = ((SUC n)*(SUC n + 1)) DIV 2 by #;
  end;
qed`;;

thm `;
!n. nsum (1..n) (\i. i) = (n * (n + 1)) DIV 2
proof
  (if 1 = 0 then 0 else 0) = (0 * (0 + 1)) DIV 2 by ARITH_TAC;
  nsum (1..0) (\i. i) = (0 * (0 + 1)) DIV 2 [A1]
    by ASM_REWRITE_TAC[NSUM_CLAUSES_NUMSEG];
  !n. nsum (1..n) (\i. i) = (n * (n + 1)) DIV 2
      ==> nsum (1..SUC n) (\i .i) = (SUC n * (SUC n + 1)) DIV 2
  proof
    let n be num;
    assume nsum (1..n) (\i. i) = (n * (n + 1)) DIV 2 [A2];
    (if 1 <= SUC n then (n * (n + 1)) DIV 2 + SUC n else (n * (n + 1)) DIV 2) =
      (SUC n * (SUC n + 1)) DIV 2 by ARITH_TAC;
  qed by ASM_REWRITE_TAC[NSUM_CLAUSES_NUMSEG],A2;
qed by INDUCT_TAC,A1`;;

let NSUM_CLAUSES_NUMSEG' = thm `;
!s. nsum(0..0) s = s 0 /\ !n. nsum(0..n + 1) s = nsum(0..n) s + s (n + 1)
proof
  !n. 0 <= SUC n by ARITH_TAC;
qed by NSUM_CLAUSES_NUMSEG,ADD1`;;

let num_INDUCTION' = REWRITE_RULE[ADD1] num_INDUCTION;;

thm `;
!s. (!i. s i = i) ==> !n. nsum(0..n) s = (n*(n + 1)) DIV 2
proof
  let s be num->num;
  assume !i. s i = i [A1];
  set X = \n. (nsum(0..n) s = (n*(n + 1)) DIV 2);
  nsum(0..0) s = s 0 by NSUM_CLAUSES_NUMSEG';
    .= 0 by A1;
    .= (0*(0 + 1)) DIV 2 by ARITH_TAC;
  X 0 [A2];
  now [A3] let n be num;
    assume X n;
    nsum(0..n + 1) s = (n*(n + 1)) DIV 2 + s (n + 1) by NSUM_CLAUSES_NUMSEG';
      .= (n*(n + 1)) DIV 2 + (n + 1) by A1;
    thus X (n + 1) by ARITH_TAC;
  end;
  !n. X n by MATCH_MP_TAC,num_INDUCTION',A2,A3;
qed`;;

