needs "Library/transc.ml";;
needs "Examples/sos.ml";;

prioritize_real();;

horizon := 1;;

let rational = new_definition
 `rational(r) = ?p q. ~(q = 0) /\ abs(r) = &p/ &q`;;

(* ======== Mizar-style version ============================================ *)

let NSQRT_2_1 = thm `;
  !p q. p*p = 2*q*q ==> q = 0
  proof
    exec MATCH_MP_TAC num_WF;
    let p be num;
    assume !p'. p' < p ==> !q. p'*p' = 2*q*q ==> q = 0 [1];
    let q be num;
    assume p*p = 2*q*q [2];
    EVEN (p*p) by EVEN_DOUBLE;
    EVEN p by EVEN_MULT;
    consider p' such that
      p = 2*p' [3] by EVEN_EXISTS;
    q*q = 2*p'*p' [4] by 2,NUM_RING;
    EVEN (q*q) by EVEN_DOUBLE;
    EVEN q by EVEN_MULT;
    consider q' such that
      q = 2*q' [5] by EVEN_EXISTS;
    p'*p' = 2*q'*q' [6] by 4,NUM_RING;
    assume ~(q = 0) [7];
    ~(p = 0) by 2,NUM_RING;
    p > 0 by ARITH_TAC;
    p' < p by 3,ARITH_TAC;
    q' = 0 by 1,6;
  qed by 5,7,MULT_EQ_0`;;

let SQRT_2_IRRATIONAL_1 = thm `;
  ~rational(sqrt(&2))
  proof
    assume rational(sqrt(&2));
    set x = abs(sqrt(&2));
    consider p q such that
      ~(q = 0) /\ x = &p/ &q [7] by rational;
    ~(&q = &0) by REAL_INJ;
    x* &q = &p [8] by 7,REAL_DIV_RMUL;
    &0 <= &2 by REAL_ARITH_TAC;
    sqrt(&2) pow 2 = &2 by SQRT_POW2;
    x pow 2 = &2 by REAL_ARITH_TAC;
    &p* &p = &2* &q* &q by 8,REAL_RING;
    p*p = 2*q*q by 8,REAL_INJ,REAL_OF_NUM_MUL;
  qed by 7,NSQRT_2_1`;;

(* ======== "automatically" converted from John's version ================== *)

let NSQRT_2_2 = thm `;
  now
    now
      let p q be num;
      assume !m q. m < p ==> m * m = 2 * q * q ==> q = 0 [1];
      assume p * p = 2 * q * q [2];
      now
        let m be num;
        assume !m' q. m' < 2 * m ==> m' * m' = 2 * q * q ==> q = 0 [3];
        assume (2 * m) * 2 * m = 2 * q * q [4];
        (2 * m) * 2 * m = 2 * q * q
            ==> (q < 2 * m ==> q * q = 2 * m * m ==> m = 0)
            ==> q = 0
          by TIMED_TAC 2 (CONV_TAC SOS_RULE);
        (q < 2 * m ==> q * q = 2 * m * m ==> m = 0) ==> q = 0
          by POP_ASSUM MP_TAC,4 from -;
        thus q = 0 by FIRST_X_ASSUM
          (MP_TAC o SPECL [parse_term "q:num"; parse_term "m:num"]),3,4;
      end;
      (?m. p = 2 * m) ==> q = 0
        by DISCH_THEN(X_CHOOSE_THEN (parse_term "m:num") SUBST_ALL_TAC),1,2;
      EVEN p ==> q = 0 by REWRITE_TAC[EVEN_EXISTS],1,2;
      (EVEN (p * p) <=> EVEN (2 * q * q)) ==> q = 0
        by REWRITE_TAC[EVEN_MULT; ARITH],1,2;
      thus q = 0 by FIRST_ASSUM(MP_TAC o AP_TERM (parse_term "EVEN")),1,2;
    end;
    !p q.
        (!m q. m < p ==> m * m = 2 * q * q ==> q = 0)
        ==> p * p = 2 * q * q
        ==> q = 0 by REPEAT STRIP_TAC;
    !p. (!m. m < p ==> (!q. m * m = 2 * q * q ==> q = 0))
        ==> (!q. p * p = 2 * q * q ==> q = 0)
      by REWRITE_TAC[RIGHT_IMP_FORALL_THM];
    thus !p q. p * p = 2 * q * q ==> q = 0 by MATCH_MP_TAC num_WF;
  end`;;

let SQRT_2_IRRATIONAL_2 = thm `;
  now
    now
      let p q be num;
      now
        assume ~(q = 0) [1];
        ~(&2 * &q * &q = &p * &p)
          by ASM_MESON_TAC[NSQRT_2_2; REAL_OF_NUM_EQ; REAL_OF_NUM_MUL];
        ~((\x. x pow 2) (sqrt (&2)) = (\x. x pow 2) (&p / &q))
          by ASM_SIMP_TAC[SQRT_POW_2; REAL_POS; REAL_POW_DIV; REAL_POW_2;
            REAL_LT_SQUARE; REAL_OF_NUM_EQ; REAL_EQ_RDIV_EQ],1;
        thus ~(sqrt (&2) = &p / &q)
          by DISCH_THEN(MP_TAC o AP_TERM (parse_term "\\x. x pow 2")),1;
      end;
      thus ~(~(q = 0) /\ sqrt (&2) = &p / &q)
        by DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC);
    end;
    !p q. ~(~(q = 0) /\ sqrt (&2) = &p / &q) by REPEAT GEN_TAC;
    thus ~rational (sqrt (&2))
      by SIMP_TAC[rational; real_abs; SQRT_POS_LE; REAL_POS; NOT_EXISTS_THM];
  end`;;

(* ======== humanized version of John's version ============================ *)

let NSQRT_2_3 = thm `;
  !p q. p*p = 2*q*q ==> q = 0
  proof
    set P = \p. !q. p*p = 2*q*q ==> q = 0;
    now
      let p be num;
      assume !m. m < p ==> P m [1];
      let q be num;
      assume p*p = 2*q*q [2];
      EVEN(2*q*q) by REWRITE_TAC,EVEN_MULT,ARITH;
      EVEN p by 2,EVEN_MULT;
      consider m such that p = 2*m [3] by EVEN_EXISTS;
      (2*m)*2*m = 2*q*q /\ (q < 2*m /\ q*q = 2*m*m ==> m = 0) ==> q = 0
        from TIMED_TAC 2 (CONV_TAC SOS_RULE);
      thus q = 0 by 1,2,3;
    end;
  qed by MATCH_MP_TAC num_WF`;;

let SQRT_2_IRRATIONAL_3 = thm `;
  ~rational(sqrt(&2))
  proof
    assume rational(sqrt(&2));
    consider p q such that ~(q = 0) /\ sqrt(&2) = &p/ &q [1]
      by rational,real_abs,SQRT_POS_LE,REAL_POS;
    (&p* &p)/(&q* &q) = &2 [2] by SQRT_POW_2,REAL_POS,REAL_POW_DIV,REAL_POW_2;
    &0 < &q* &q by 1,REAL_LT_SQUARE,REAL_OF_NUM_EQ;
    &2*(&q* &q) = (&p* &p) by 2,REAL_EQ_RDIV_EQ;
  qed by 1,NSQRT_2_3,REAL_OF_NUM_EQ,REAL_OF_NUM_MUL`;;

