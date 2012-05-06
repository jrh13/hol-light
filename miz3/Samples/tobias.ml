prioritize_real();;

let rational = new_definition
  `rational(r) <=> ?p q. ~(q = 0) /\ (abs(r) = &p / &q)`;;

horizon := 1;;

let TOBIAS = thm `;
  let f be real->real;
  assume f(&0) = &1 [1];
  assume !x y. f(x + y + &1) = f x + f y [2];
  let r be real;
  assume rational r [3];
  thus f r = r + &1
  proof
    set g = \x. f(x) - &1;
    g(&0) = &0 [4] by 1,REAL_FIELD;
    now [5] let x be real;
      x + &1 = x + &0 + &1 by REAL_FIELD;
      g(x + &1) = (f x + f(&0)) - &1 by 2;
      thus ... = g x + &1 by 1,REAL_FIELD;
    end;
    now [6] let x be real;
      (x - &1) + &1 = x [7] by REAL_FIELD;
      g(x - &1) = (g(x - &1) + &1) - &1 by REAL_FIELD;
      thus ... = g(x) - &1 by 5,7;
    end;
    now [8] let x y be real;
      x + y = (x + y + &1) - &1 by REAL_FIELD;
      g(x + y) = (f x + f y) - &1 - &1 by 2,6;
      thus ... = g x + g y by 2,REAL_FIELD;
    end;
    now [9] let x be real;
      g(&0*x) = &0*(g x) [10] by 4,REAL_MUL_LZERO;
      now [11]
        let n be num;
        assume g(&n*x) = &n*(g x) [12];
        &(SUC n) = &n + &1 [13] by ADD1,REAL_OF_NUM_ADD;
        &(SUC n)*x = &n*x + x by REAL_FIELD;
        g(&(SUC n)*x) = &n*(g x) + g x by 8,12;
        thus ... = &(SUC n)*g x by 13,REAL_FIELD;
      end;
      thus !n. g(&n*x) = &n*g(x) by INDUCT_TAC,10,11;
    end;
    &1 = &0 + &1 /\ -- &1 = &0 - &1 by REAL_FIELD;
    g(&1) = &1 /\ g(-- &1) = -- &1 [14] by 4,5,6;
    consider n m such that ~(m = 0) /\ (abs r = &n/ &m) [15]
      by 3,rational;
    0 < m by ARITH_TAC;
    &0 < &m [16] by REAL_OF_NUM_LT;
    cases by REAL_FIELD;
    suppose &0 <= r;
      r = (&n* &1)/ &m [17] by 15,REAL_FIELD;
      &m*r = &n* &1 [18] by 16,REAL_FIELD;
      &m*g(r) = &n* &1 by 9,14,18;
      f r = r + &1 by 16,17,REAL_FIELD;
    qed;
    suppose r < &0;
      r = (&n*(-- &1))/ &m [19] by 15,REAL_FIELD;
      &m*r = &n*(-- &1) [20] by 16,REAL_FIELD;
      &m*g(r) = &n*(-- &1) by 9,14,20;
      f r = r + &1 by 16,19,REAL_FIELD;
    qed;
  end`;;

