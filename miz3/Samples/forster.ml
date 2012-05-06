(* ======== translation of "The shortest?" from Examples/forster.ml ======== *)

horizon := 0;;

let FORSTER_PUZZLE_1 = thm `;
  let f be num->num;
  thus (!n. f(n + 1) > f(f(n))) ==> !n. f(n) = n
  proof
    assume !n. f(n + 1) > f(f(n));
    !n. f(f(n)) < f(SUC n) [1] by -,GT,ADD1;
    !m n. m <= f(n + m) [2]
    proof
      !n. 0 <= f(n + 0) [3] by LE_0,ADD_CLAUSES,LE_SUC_LT;
      now let m be num;
        assume !n. m <= f(n + m);
        !n. m < f(SUC (n + m)) by -,1,LET_TRANS,SUB_ADD;
        thus !n. SUC m <= f(n + SUC m) by -,LE_0,ADD_CLAUSES,LE_SUC_LT;
      end;
    qed by INDUCT_TAC,-,3;
    !n. f(n) < f(SUC n) [4] by -,1,LET_TRANS,LE_TRANS,ADD_CLAUSES;
    !m n. f(m) < f(n) ==> m < n
    proof
      !n. f(0) < f(n) ==> 0 < n [5] by LT_LE,LE_0,LTE_TRANS,LE_SUC_LT;
      now let m be num;
        assume !n. f(m) < f(n) ==> m < n;
        thus !n. f(SUC m) < f(n) ==> SUC m < n
          by -,4,LT_LE,LE_0,LTE_TRANS,LE_SUC_LT;
      end;
    qed by INDUCT_TAC,-,5;
  qed by -,1,2,LE_ANTISYM,ADD_CLAUSES,LT_SUC_LE`;;

(* ======== long-winded informal proof ===================================== *)

(*

Suppose that f(f(n)) < f(n + 1) for all n.  We want to
show that f has to be the identity.  We will do this by
successively establishing two properties of f (both in a
certain sense being "monotonicity of f"):

        n <= f(n)

        m < n ==> f(m) < f(n)

The first is the harder one to prove.  The second is easy,
but the proof uses the first.  Once we know the second
property we know so much about f that the result easily
follows.

To prove the first, suppose by contradiction that there is a
counterexample, so there is an n with f "going backwards",
i.e., with f(n) < n.  Take such a counterexample with f(n)
minimal.  (That this minimality is the right one to focus
on is the key to the whole proof for me.  Of course one can
present this proof the other way around -- as an induction --
but the intuition of a descending chain of counterexamples
I find much easier to remember.)  Now from the relation

        f(f(n - 1)) < f(n)

it seems reasonable to look for an n' with f going backwards
that has an image less than f(n).  So look at

        n - 1  |->  f(n - 1)  |->  f(f(n - 1))

and distinguish how f(n - 1) compares to f(n).  If it's less,
then the left mapping goes backward to an image < f(n).
(To see that it goes backward, use that f(n) < n, so that
f(n) <= n - 1.)  If it's not less, then the right mapping
goes backward to an image < f(n).  In both cases we have
a contradiction with the minimality of our choice of n.

The second kind of monoticity now follows using a trivial
transitivity:

        f(n) <= f(f(n)) < f(n + 1)

This shows that f(n) < f(n + 1) for all n, from with the
monotonicity of the whole function directly follows.

Finally to show that f has to be the identity, notice that
a strictly monotonic function always has the property that

        n <= f(n)

(Of course we knew this already, but I like to just think
about the strict monotonicity of f at this point.)

However we also can get an upper bound on f(n).  A strictly
monototic function always has a strictly monotonic inverse,
and so from the key property

        f(f(n)) < f(n + 1)

it follows that

        f(n) < n + 1

Together this means that we have to have that f(n) = n.

*)

(* ======== formal proof sketch of this proof ============================== *)

horizon := -1;;
sketch_mode := true;;

let FORSTER_PUZZLE_SKETCH = ref None;;

FORSTER_PUZZLE_SKETCH := Some `;
  let f be num->num;
  assume !n. f(f(n)) < f(n + 1);
  thus !n. f(n) = n
  proof
    !n. n <= f(n)
    proof
      assume ~thesis;
      ?n. f(n) < n;
      consider n such that f(n) < n /\
        !m. f(m) < m ==> f(n) <= f(m);
      cases;
      suppose f(n - 1) < f(n);
        f(n - 1) < n - 1 /\ f(n - 1) < f(n)
        proof
          f(n) < n;
          f(n) <= n - 1;
        qed;
        thus F;
      end;
      suppose f(n) <= f(n - 1);
        f(f(n - 1)) < f(n - 1) /\ f(f(n - 1)) < f(n);
        thus F;
      end;
    end;
    !m n. m < n ==> f(m) < f(n)
    proof
      now
        let n be num;
        f(n) <= f(f(n)) /\ f(f(n)) < f(n + 1);
        thus f(n) < f(n + 1);
      end;
    qed;
    let n be num;
    n <= f(n);
    !m n. f(m) < f(n) ==> m < n;
    f(f(n)) < f(n + 1);
    f(n) < n + 1;
    thus f(n) = n;
  end`;;

sketch_mode := false;;

(* ======== formalization from this formal proof sketch ==================== *)

horizon := 1;;

let FORSTER_PUZZLE_2 = thm `;
  let f be num->num;
  assume !n. f(f(n)) < f(n + 1) [1];
  thus !n. f(n) = n
  proof
    !n. n <= f(n) [2]
    proof
      assume ~thesis;
      ?n. f(n) < n by NOT_LE;
      ?fn n. f(n) = fn /\ f(n) < n;
      consider fn such that (?n. f(n) = fn /\ f(n) < n) /\
        !fm. fm < fn ==> ~(?m. f(m) = fm /\ f(m) < m) [3]
          by REWRITE_TAC,GSYM num_WOP;
      consider n such that f(n) = fn /\ f(n) < n;
      f(n) < n /\ !m. f(m) < m ==> f(n) <= f(m) [4] by 3,NOT_LE;
      cases;
      suppose f(n - 1) < f(n) [5];
        f(n - 1) < n - 1 /\ f(n - 1) < f(n)
        proof
          f(n) < n by 4;
          f(n) <= n - 1 by ARITH_TAC;
        qed by 5,LTE_TRANS;
        thus F by 4,NOT_LE;
      end;
      suppose f(n) <= f(n - 1) [6];
        0 < n by ARITH_TAC,4;
        (n - 1) + 1 = n by ARITH_TAC;
        f(f(n - 1)) < f(n) by 1;
        f(f(n - 1)) < f(n - 1) /\ f(f(n - 1)) < f(n) by ARITH_TAC,6;
        thus F by 4,NOT_LE;
      end;
    end;
    !m n. m < n ==> f(m) < f(n) [7]
    proof
      now
        let n be num;
        f(n) <= f(f(n)) /\ f(f(n)) < f(n + 1) by 1,2;
        thus f(n) < f(SUC n) by ARITH_TAC;  // modified from f(n) < f(n + 1)
      end;
    qed by LT_TRANS,
      SPEC (parse_term "\\m n. (f:num->num)(m) < f(n)") TRANSITIVE_STEPWISE_LT;
    let n be num;
    n <= f(n) [8] by 2;  // really should be an induction proof from 7
    !m n. f(m) < f(n) ==> m < n [9] by 7,LE_LT,NOT_LE;
    f(f(n)) < f(n + 1) by 1;
    f(n) < n + 1 by 9;
    thus f(n) = n by ARITH_TAC,8;
  end`;;

(* ======== ... and a slightly compressed version ========================== *)

horizon := 1;;

let FORSTER_PUZZLE_3 = thm `;
  let f be num->num;
  assume !n. f(f(n)) < f(n + 1) [1];
  !n. n <= f(n) [2]
  proof
    assume ~thesis;
    ?fn n. f(n) = fn /\ f(n) < n by NOT_LE;
    consider fn such that (?n. f(n) = fn /\ f(n) < n) /\
      !fm. fm < fn ==> ~(?m. f(m) = fm /\ f(m) < m) [3]
        by REWRITE_TAC,GSYM num_WOP;
    consider n such that f(n) = fn /\ f(n) < n [4];
    cases;
    suppose f(n - 1) < f(n) [5];
      f(n - 1) < n - 1 by ARITH_TAC,4;
      thus F by 3,4,5;
    end;
    suppose f(n) <= f(n - 1) [6];
      (n - 1) + 1 = n by ARITH_TAC,4;
      thus F by 1,3,4,6,LTE_TRANS;
    end;
  end;
  !n. f(n) < f(SUC n) by 1,2,ADD1,LET_TRANS;
  !m n. m < n ==> f(m) < f(n) by LT_TRANS,
    SPEC (parse_term "\\m n. (f:num->num)(m) < f(n)") TRANSITIVE_STEPWISE_LT;
  !m n. f(m) < f(n) ==> m < n by LE_LT,NOT_LE;
  thus !n. f(n) = n by 1,2,ADD1,LE_ANTISYM,LT_SUC_LE`;;

(* ======== Mizar formalization from the formal proof sketch =============== *)

(*

environ
  vocabularies RELAT_1, FUNCT_1, ARYTM, ARYTM_1, ORDINAL2;
  notations ORDINAL1, RELSET_1, FUNCT_2, NUMBERS, XCMPLX_0, XXREAL_0, NAT_1,
    VALUED_0;
  constructors XXREAL_0, INT_1, PARTFUN1, VALUED_0, MEMBERED, RELSET_1;
  registrations XBOOLE_0, RELAT_1, FUNCT_1, ORDINAL1, XXREAL_0, XREAL_0,
    NAT_1, INT_1, VALUED_0, MEMBERED;
  requirements NUMERALS, REAL, SUBSET, ARITHM;
  theorems XXREAL_0, XREAL_1, INT_1, NAT_1, VALUED_0, VALUED_1, FUNCT_2,
    ORDINAL1;
  schemes NAT_1;

begin
  reserve n,m,fn,fm for natural number;
  reserve f for Function of NAT,NAT;

theorem
  (for n holds f.(f.n) < f.(n + 1)) implies for n holds f.n = n
proof
  assume
A1: for n holds f.(f.n) < f.(n + 1);
A2: for n holds n <= f.n
  proof
    assume
A3:   not thesis;
    defpred P[Nat] means ex n st f.n < n & f.n = $1;
A4: ex fn st P[fn] by A3;
    consider fn being Nat such that
A5:   P[fn] & for fm being Nat st P[fm] holds fn <= fm from NAT_1:sch 5(A4);
    consider n such that
A6:   f.n < n & f.n = fn by A5;
    n >= 0 + 1 by A6,NAT_1:13;
    then n - 1 >= 0 by XREAL_1:21;
    then n - 1 in NAT by INT_1:16;
    then reconsider m = n - 1 as natural number;
    per cases;
    suppose
A7:     f.m < f.n;
      f.n < m + 1 by A6;
      then f.n <= m by NAT_1:13;
      then f.m < m by A7,XXREAL_0:2;
      hence contradiction by A5,A6,A7;
    end;
    suppose
A8:     f.n <= f.m;
A9:   f.(f.m) < f.(m + 1) by A1;
      then f.(f.m) < f.m by A8,XXREAL_0:2;
      hence contradiction by A5,A6,A9;
    end;
  end;
  now
    let n;
    f.n <= f.(f.n) & f.(f.n) < f.(n + 1) by A1,A2;
    hence f.n < f.(n + 1) by XXREAL_0:2;
  end;
  then reconsider f as increasing Function of NAT,NAT by VALUED_1:def 13;
A10: now
    let m,n;
    dom f = NAT & m in NAT & n in NAT by FUNCT_2:def 1,ORDINAL1:def 13;
    hence f.m < f.n implies m < n by VALUED_0:def 15;
  end;
  let n;
  f.(f.n) < f.(n + 1) by A1;
  then f.n < n + 1 by A10;
  then n <= f.n & f.n <= n by A2,NAT_1:13;
  hence thesis by XXREAL_0:1;
end;

*)

(* ======== miz3 formalization close to the Mizar formalization ============ *)

horizon := 0;;

let FORSTER_PUZZLE_4 = thm `;
  !f. (!n. f(f(n)) < f(n + 1)) ==> !n. f(n) = n
proof
  let f be num->num;
  assume !n. f(f(n)) < f(n + 1) [1];
  !n. n <= f(n) [2]
  proof
    assume ~thesis [3];
    set P = \fn. ?n. f(n) < n /\ f(n) = fn [P];
    ?fn. P(fn) [4] by 3,P,NOT_LE;
    consider fn such that P(fn) /\ !fm. P(fm) ==> fn <= fm [5]
      by 4,num_WOP,NOT_LE;
    consider n such that f(n) < n /\ f(n) = fn [6] by P,5;
    set m = n - 1;
    n = m + 1 [m] by ARITH_TAC,6;       // replaces the reconsider
    cases;
    suppose f(m) < f(n) [7];
      f(n) < m + 1 by ARITH_TAC,6;
      f(n) <= m by ARITH_TAC,-;
      f(m) < m by ARITH_TAC,-,7;
      f(n) <= f(m) by -,P,5,6;          // extra step
      thus F by ARITH_TAC,-,7;
    end;
    suppose f(n) <= f(m) [8];
      f(f(m)) < f(m + 1) [9] by 1;
      f(f(m)) < f(m) by -,m,8,LTE_TRANS;
      f(n) <= f(f(m)) by -,P,5,6;       // extra step
      thus F by -,m,9,NOT_LE;
    end;
  end;
  now
    let n be num;
    f(n) <= f(f(n)) /\ f(f(n)) < f(n + 1) by 1,2;
    thus f(n) < f(n + 1) by ARITH_TAC,-;
  end;
  !n. f(n) < f(SUC n) by -,ADD1;        // extra step
  !m n. m < n ==> f(m) < f(n) by -,LT_TRANS,
    SPEC (parse_term "\\m n. (f:num->num)(m) < f(n)") TRANSITIVE_STEPWISE_LT;
                                        // replaces the reconsider
  now [10]
    let m n be num;
    thus f(m) < f(n) ==> m < n by -,LE_LT,NOT_LE;
  end;
  let n be num;
  f(f(n)) < f(n + 1) by 1;
  f(n) < n + 1 by -,10;
  n <= f(n) /\ f(n) <= n by -,2,ADD1,LT_SUC_LE;
  thus thesis by ARITH_TAC,-;
end`;;

(* ======== formalization following Tobias & Sean's version ================ *)

horizon := 3;;

let num_MONO_LT_SUC = thm `;
  let f be num->num;
  assume !n. f(n) < f(SUC n);
  !n m. m < n ==> f(m) < f(n) by LT_TRANS,
    SPEC (parse_term "\\m n. (f:num->num)(m) < f(n)") TRANSITIVE_STEPWISE_LT;
  thus !n m. m < n <=> f(m) < f(n) by LE_LT,NOT_LE`;;

let FORSTER_PUZZLE_5 = thm `;
  let f be num->num;
  assume !n. f(f(n)) < f(SUC(n));
  !n m. n <= m ==> n <= f(m)
  proof
    now let n be num; assume !m. n <= m ==> n <= f(m);
      !m. SUC n <= m ==> ?k. m = SUC k by num_CASES,LT,LE_SUC_LT;
      thus !m. SUC n <= m ==> SUC n <= f(m) by LE_SUC,LET_TRANS,LE_SUC_LT;
    end;
    !m. 0 <= m ==> 0 <= f(m);
  qed by INDUCT_TAC;
  !n. f(n) < f(SUC n) by LE_REFL,LET_TRANS;
  thus !n. f(n) = n by num_MONO_LT_SUC,LT_SUC_LE,LE_ANTISYM`;;

