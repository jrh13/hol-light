horizon := -1;;

let FOO = thm `;
  !x n. x pow n = &1 <=> abs x = &1 /\ (x < &0 ==> EVEN n) \/ n = 0 [1]
  proof
    let x be real;
    let n be num;
    n = 0
    ==> (x pow n = &1 <=> abs x = &1 /\ (x < &0 ==> EVEN n) \/ n = 0) [2]
    proof
      assume n = 0 [3];
    qed by ASM_REWRITE_TAC[real_pow],3;
    ~(n = 0)
    ==> (x pow n = &1 <=> abs x = &1 /\ (x < &0 ==> EVEN n) \/ n = 0) [4]
    proof
      assume ~(n = 0) [5];
      abs x = &1 ==> (x pow n = &1 <=> abs x = &1 /\ (x < &0 ==> EVEN n)) [6]
      proof
        assume abs x = &1 [7];
        &1 < &0 ==> EVEN n [8] by REAL_ARITH_TAC,5;
        &1 pow n = &1 <=> &1 < &0 ==> EVEN n [9]
          by ASM_REWRITE_TAC[REAL_POW_NEG; REAL_POW_ONE],5 from 8;
        EVEN n ==> (&1 = &1 <=> -- &1 < &0 ==> T) [10]
        proof
          assume EVEN n [11];
        qed by ASM_REWRITE_TAC[],5,11;
        ~EVEN n ==> (-- &1 = &1 <=> -- &1 < &0 ==> F) [12]
        proof
          assume ~EVEN n [13];
          -- &1 = &1 <=> ~(-- &1 < &0) [14] by REAL_ARITH_TAC,5,13;
        qed by ASM_REWRITE_TAC[],5,13 from 14;
        (if EVEN n then &1 else -- &1) = &1 <=> -- &1 < &0 ==> EVEN n [15]
          by REPEAT COND_CASES_TAC,5 from 10,12;
        -- &1 pow n = &1 <=> -- &1 < &0 ==> EVEN n [16]
          by ASM_REWRITE_TAC[REAL_POW_NEG; REAL_POW_ONE],5 from 15;
        x pow n = &1 <=> x < &0 ==> EVEN n [17]
          by FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC o MATCH_MP (REAL_ARITH (parse_term "abs x = a ==> x = a \\/ x = --a"))),5,7
          from 9,16;
        x pow n = &1 <=> abs x = &1 /\ (x < &0 ==> EVEN n) [18]
          by ASM_REWRITE_TAC[],5,7 from 17;
      qed by ALL_TAC,5,7 from 18;
      ~(abs x = &1)
      ==> (x pow n = &1 <=> abs x = &1 /\ (x < &0 ==> EVEN n)) [19]
      proof
        assume ~(abs x = &1) [20];
      qed by ASM_MESON_TAC[REAL_POW_EQ_1_IMP],5,20;
::                                                #2
:: 2: inference time-out
    qed by ASM_REWRITE_TAC[real_pow],5 from 18;
::                                            #4
:: 4: unknown label
  qed by ASM_CASES_TAC (parse_term "n = 0") from 2,4;`;;
