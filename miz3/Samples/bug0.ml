prioritize_num();;

let EGCD_INVARIANT = thm `;
  !m n d. d divides egcd(m,n) <=> d divides m /\ d divides n
  proof
    let m n be num;
    (!m'' n'.
         m'' + n' < m + n
         ==> (!d. d divides egcd (m'',n') <=>
             d divides m'' /\ d divides n'))
    ==> (!d. d divides egcd (m,n) <=> d divides m /\ d divides n) [1]
    proof
      assume !m'' n'.
                 m'' + n' < m + n
                 ==> (!d. d divides egcd (m'',n') <=>
                      d divides m'' /\ d divides n') [2];
      !d. d divides
          (if m = 0
           then n
           else
          if n = 0
          then m
          else if m <= n then egcd (m,n - m) else egcd (m - n,n)) <=>
          d divides m /\ d divides n [3]
      proof
        let d be num;
        m = 0 ==> (d divides n <=> d divides m /\ d divides n) [4]
          by DIVIDES_0;
        ~(m = 0)
        ==> (d divides
             (if n = 0
              then m
              else
             if m <= n then egcd (m,n - m) else egcd (m - n,n)) <=>
             d divides m /\ d divides n) [5]
        proof
          assume ~(m = 0) [6];
          n = 0 ==> (d divides m <=> d divides m /\ d divides n) [7]
            by DIVIDES_0;
          ~(n = 0)
          ==> (d divides
               (if m <= n then egcd (m,n - m) else egcd (m - n,n)) <=>
               d divides m /\ d divides n) [8]
          proof
            assume ~(n = 0) [9];
            m <= n
            ==> (d divides egcd (m,n - m) <=>
                 d divides m /\ d divides n) [10]
            proof
              assume m <= n;
              m + (n - m) < m + n by ARITH_TAC,6;
            qed by #;
            ~(m <= n)
            ==> (d divides egcd (m - n,n) <=>
                 d divides m /\ d divides n) [11]
            proof
              assume ~(m <= n);
              (m - n) + n < m + n by ARITH_TAC,9;
              d divides egcd (m - n,n) <=> d divides m - n /\ d divides n
                by 2;
              ... <=> d divides (m - n) + n /\ d divides n by DIVIDES_ADD;
::                                                                       #1
:: 1: inference error
            qed by 2,DIVIDES_SUB;
::                              #1
          qed by COND_CASES_TAC from 10,11;
        qed by COND_CASES_TAC from 7,8;
      qed by COND_CASES_TAC from 4,5;
    qed by ONCE_REWRITE_TAC[egcd] from 3;
  qed by WF_INDUCT_TAC (parse_term "m + n") from 1;
::                                                #1
`;;
