horizon := 0;;

let SUC_INJ_1 = thm `;
  now
    now [1]
      let m n be num;
      now [2]
        assume mk_num (IND_SUC (dest_num m)) =
               mk_num (IND_SUC (dest_num n)) [3];
        now [4]
          let p be num;
          NUM_REP (dest_num p) [5]
            by REWRITE_TAC[fst num_tydef; snd num_tydef] ;
          thus NUM_REP (IND_SUC (dest_num p))
            by MATCH_MP_TAC (CONJUNCT2 NUM_REP_RULES) from 5;
        end;
        !p. NUM_REP (IND_SUC (dest_num p)) [6] by GEN_TAC from 4;
        now [7]
          assume !p. dest_num (mk_num (IND_SUC (dest_num p))) =
                     IND_SUC (dest_num p) [8];
          mk_num (dest_num m) = mk_num (dest_num n) ==> m = n [9]
            by REWRITE_TAC[fst num_tydef];
          dest_num m = dest_num n ==> m = n [10]
            by DISCH_THEN(MP_TAC o AP_TERM (parse_term "mk_num")) from 9;
          thus dest_num (mk_num (IND_SUC (dest_num m))) =
               dest_num (mk_num (IND_SUC (dest_num n)))
               ==> m = n by ASM_REWRITE_TAC[IND_SUC_INJ],8 from 10;
        end;
        (!p. dest_num (mk_num (IND_SUC (dest_num p))) =
               IND_SUC (dest_num p))
          ==> dest_num (mk_num (IND_SUC (dest_num m))) =
              dest_num (mk_num (IND_SUC (dest_num n)))
          ==> m = n [11] by DISCH_TAC from 7;
        (!p. NUM_REP (IND_SUC (dest_num p)))
          ==> dest_num (mk_num (IND_SUC (dest_num m))) =
              dest_num (mk_num (IND_SUC (dest_num n)))
          ==> m = n [12] by REWRITE_TAC[fst num_tydef; snd num_tydef] from 11;
        dest_num (mk_num (IND_SUC (dest_num m))) =
          dest_num (mk_num (IND_SUC (dest_num n)))
          ==> m = n [13]
            by SUBGOAL_THEN (parse_term "!p. NUM_REP (IND_SUC (dest_num p))")
              MP_TAC from 6,12;
        thus m = n
          by POP_ASSUM(MP_TAC o AP_TERM (parse_term "dest_num")),3 from 13;
      end;
      mk_num (IND_SUC (dest_num m)) = mk_num (IND_SUC (dest_num n))
        ==> m = n [14] by DISCH_TAC from 2;
      now [15]
        assume m = n [16];
        thus mk_num (IND_SUC (dest_num m)) =
             mk_num (IND_SUC (dest_num n)) by ASM_REWRITE_TAC[],16;
      end;
      m = n
        ==> mk_num (IND_SUC (dest_num m)) =
            mk_num (IND_SUC (dest_num n)) [17] by DISCH_TAC from 15;
      mk_num (IND_SUC (dest_num m)) = mk_num (IND_SUC (dest_num n)) <=>
        m = n [18] by EQ_TAC from 14,17;
      thus SUC m = SUC n <=> m = n by REWRITE_TAC[SUC_DEF] from 18;
    end;
    thus !m n. SUC m = SUC n <=> m = n by REPEAT GEN_TAC from 1;
  end;
`;;

let SUC_INJ_2 = thm `;
  !m n. SUC m = SUC n <=> m = n [1]
  proof
    let m n be num;
    mk_num (IND_SUC (dest_num m)) = mk_num (IND_SUC (dest_num n))
    ==> m = n [2]
    proof
      assume mk_num (IND_SUC (dest_num m)) =
             mk_num (IND_SUC (dest_num n)) [3];
      !p. NUM_REP (IND_SUC (dest_num p)) [4]
      proof
        let p be num;
        NUM_REP (dest_num p) [5]
          by REWRITE_TAC[fst num_tydef; snd num_tydef];
      qed by MATCH_MP_TAC (CONJUNCT2 NUM_REP_RULES) from 5;
      (!p. dest_num (mk_num (IND_SUC (dest_num p))) =
           IND_SUC (dest_num p))
      ==> dest_num (mk_num (IND_SUC (dest_num m))) =
          dest_num (mk_num (IND_SUC (dest_num n)))
      ==> m = n [6]
      proof
        assume !p. dest_num (mk_num (IND_SUC (dest_num p))) =
                   IND_SUC (dest_num p) [7];
        mk_num (dest_num m) = mk_num (dest_num n) ==> m = n [8]
          by REWRITE_TAC[fst num_tydef];
        dest_num m = dest_num n ==> m = n [9]
          by DISCH_THEN(MP_TAC o AP_TERM (parse_term "mk_num")) from 8;
      qed by ASM_REWRITE_TAC[IND_SUC_INJ],* from 9;
      (!p. NUM_REP (IND_SUC (dest_num p)))
      ==> dest_num (mk_num (IND_SUC (dest_num m))) =
          dest_num (mk_num (IND_SUC (dest_num n)))
      ==> m = n [10] by REWRITE_TAC[fst num_tydef; snd num_tydef] from 6;
      dest_num (mk_num (IND_SUC (dest_num m))) =
      dest_num (mk_num (IND_SUC (dest_num n)))
      ==> m = n [11]
        by SUBGOAL_THEN (parse_term "!p. NUM_REP (IND_SUC (dest_num p))")
          MP_TAC
        from 4,10;
    qed by POP_ASSUM(MP_TAC o AP_TERM (parse_term "dest_num")),3 from 11;
    m = n
    ==> mk_num (IND_SUC (dest_num m)) = mk_num (IND_SUC (dest_num n)) [12]
    proof
      assume m = n [13];
    qed by ASM_REWRITE_TAC[],*;
    mk_num (IND_SUC (dest_num m)) = mk_num (IND_SUC (dest_num n)) <=>
    m = n [14] by EQ_TAC from 2,12;
  qed by REWRITE_TAC[SUC_DEF] from 14;`;;

let num_INDUCTION_ = thm `;
  now [1]
    let P be num->bool;
    let n be num;
    assume P _0;
    assume !n. P n ==> P (SUC n);
    now [2]
      let i be ind;
      assume NUM_REP i;
      assume P (mk_num i);
      NUM_REP i [3] by ASM_REWRITE_TAC[],*;
      thus NUM_REP (IND_SUC i)
        by MATCH_MP_TAC(CONJUNCT2 NUM_REP_RULES) from 3;
    end;
    now [4]
      let i be ind;
      assume NUM_REP i;
      assume P (mk_num i);
      NUM_REP i [5] by FIRST_ASSUM MATCH_ACCEPT_TAC,*;
      dest_num (mk_num i) = i [6] by REWRITE_TAC[GSYM(snd num_tydef)] from 5;
      i = dest_num (mk_num i) [7] by CONV_TAC SYM_CONV from 6;
      mk_num (IND_SUC i) = mk_num (IND_SUC (dest_num (mk_num i))) [8]
        by REPEAT AP_TERM_TAC from 7;
      mk_num (IND_SUC i) = SUC (mk_num i) [9] by REWRITE_TAC[SUC_DEF] from 8;
      P (mk_num i) [10] by FIRST_ASSUM MATCH_ACCEPT_TAC,*;
      P (SUC (mk_num i)) [11] by FIRST_ASSUM MATCH_MP_TAC,* from 10;
      thus P (mk_num (IND_SUC i))
        by SUBGOAL_THEN (parse_term "mk_num(IND_SUC i) = SUC(mk_num i)")
           SUBST1_TAC
        from 9,11;
    end;
    !i. NUM_REP i /\ P (mk_num i)
          ==> NUM_REP (IND_SUC i) /\ P (mk_num (IND_SUC i)) [12]
      by REPEAT STRIP_TAC from 2,4;
    (NUM_REP (dest_num n)
       ==> NUM_REP (dest_num n) /\ P (mk_num (dest_num n)))
      ==> P n [13] by REWRITE_TAC[fst num_tydef; snd num_tydef];
    (!a. NUM_REP a ==> NUM_REP a /\ P (mk_num a)) ==> P n [14]
      by DISCH_THEN(MP_TAC o SPEC (parse_term "dest_num n")) from 13;
    ((!i. NUM_REP i /\ P (mk_num i)
            ==> NUM_REP (IND_SUC i) /\ P (mk_num (IND_SUC i)))
       ==> (!a. NUM_REP a ==> NUM_REP a /\ P (mk_num a)))
      ==> P n [15]
      by W(C SUBGOAL_THEN (fun t -> REWRITE_TAC[t]) o funpow 2 lhand o snd)
      from 12,14;
    ((\i. NUM_REP i /\ P (mk_num i)) IND_0 /\
       (!i. (\i. NUM_REP i /\ P (mk_num i)) i
            ==> (\i. NUM_REP i /\ P (mk_num i)) (IND_SUC i))
       ==> (!a. NUM_REP a ==> (\i. NUM_REP i /\ P (mk_num i)) a))
      ==> P n [16] by ASM_REWRITE_TAC[GSYM ZERO_DEF; NUM_REP_RULES],* from 15;
    thus P n by MP_TAC (SPEC (parse_term
      "\\i. NUM_REP i /\\ P(mk_num i):bool") NUM_REP_INDUCT) from 16;
  end;
  thus !P. P(_0) /\ (!n. P(n) ==> P(SUC n)) ==> !n. P n
    by REPEAT STRIP_TAC from 1;
`;;

let num_RECURSION_STD = thm `;
  !e:Z f. ?fn. (fn 0 = e) /\ (!n. fn (SUC n) = f n (fn n))
  proof
    !e:Z f. ?fn. fn 0 = e /\ (!n. fn (SUC n) = f n (fn n)) [1]
    proof
      let e be Z;
      let f be num->Z->Z;
      (?fn. fn 0 = e /\ (!n. fn (SUC n) = (\z n. f n z) (fn n) n))
        ==> (?fn. fn 0 = e /\ (!n. fn (SUC n) = f n (fn n))) [2]
        by REWRITE_TAC[];
    qed by MP_TAC(ISPECL [(parse_term "e:Z");
      (parse_term "(\\z n. (f:num->Z->Z) n z)")] num_RECURSION) from 2;
  qed by REPEAT GEN_TAC from 1;
`;;

