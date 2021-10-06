
prioritize_real();;

let (TRY_RULE:(thm->thm) -> (thm->thm)) =
        fun rl t -> try (rl t) with _ -> t;;


let REAL_MUL_RTIMES =
        prove ((`!x a b.
                (((~(x=(&0))==>(a*x = b*x)) /\ ~(x=(&0))) ==>  (a = b))`),
                MESON_TAC[REAL_EQ_MUL_RCANCEL]);;


let GEOMETRIC_SUM = prove(
        `!m n x.(~(x=(&1)) ==>
        (sum(m,n) (\k.(x pow k)) = ((x pow m) - (x pow (m+n)))/((&1)-x)))`,
        let tac1 =
        GEN_TAC
        THEN INDUCT_TAC
        THEN GEN_TAC
        THEN DISCH_TAC
        THEN (REWRITE_TAC
          [sum_DEF;real_pow;ADD_CLAUSES;real_div;REAL_SUB_RDISTRIB;
                REAL_SUB_REFL]) in
        let tac2 =
         (RULE_ASSUM_TAC (TRY_RULE (SPEC (`x:real`))))
        THEN (UNDISCH_EL_TAC 1)
        THEN (UNDISCH_EL_TAC 0)
        THEN (TAUT_TAC (`(A==>(B==>C))    ==> (A ==> ((A==>B) ==>C))`))
        THEN (REPEAT DISCH_TAC)
        THEN (ASM_REWRITE_TAC[real_div])
        THEN (ABBREV_TAC (`a:real = x pow m`))
        THEN (ABBREV_TAC (`b:real = x pow (m+n)`)) in
        let tac3 =
             (MATCH_MP_TAC (SPEC (`&1 - x`) REAL_MUL_RTIMES))
        THEN CONJ_TAC
        THENL [ALL_TAC; (UNDISCH_TAC (`~(x = (&1))`))
          THEN (ACCEPT_TAC (REAL_ARITH (`~(x=(&1)) ==> ~((&1 - x = (&0)))`)))]
        THEN (REWRITE_TAC
          [GSYM REAL_MUL_ASSOC;REAL_ADD_RDISTRIB;REAL_SUB_RDISTRIB])
        THEN (SIMP_TAC[REAL_MUL_LINV])
        THEN DISCH_TAC
        THEN (REWRITE_TAC
          [REAL_SUB_LDISTRIB;REAL_MUL_LID;REAL_MUL_RID;REAL_MUL_ASSOC])
        THEN (ACCEPT_TAC (REAL_ARITH (`a - b + b - b*x = a - x*b`))) in
        (tac1 THEN tac2 THEN tac3));;


pop_priority();;
