horizon := 1;;

thm `;
  !R. (!x. R x x) /\ (!x y z. R x y /\ R y z ==> R x z)
       ==> ((!m n. m <= n ==> R m n) <=> (!n. R n (SUC n)))
  proof
   let R be num->num->bool;
   assume !x. R x x [1];
   assume !x y z. R x y /\ R y z ==> R x z [2];
   !n. n <= SUC n by ARITH_TAC;
   (!m n. m <= n ==> R m n) ==> (!n. R n (SUC n)) [3] by SIMP_TAC;
   now
    assume !n. R n (SUC n) [4];
    !m n d. n = m + d ==> R m (m + d)
    proof
     let m be num;
     R m m by MESON_TAC,1;
     R m (m + 0) [5] by REWRITE_TAC,ADD_CLAUSES;
     !d. R m (m + d) ==> R m (m + SUC d)
     proof
      let d be num;
      assume R m (m + d);
      R m (SUC (m + d)) by MESON_TAC,2,4;
     qed by REWRITE_TAC,ADD_CLAUSES;
     !d. R m (m + d) by INDUCT_TAC,5;
     !d n. n = m + d ==> R m (m + d)
      by REWRITE_TAC,LEFT_FORALL_IMP_THM,EXISTS_REFL,ADD_CLAUSES;
    qed by ONCE_REWRITE_TAC,SWAP_FORALL_THM;
    thus !m n. m <= n ==> R m n by SIMP_TAC,LE_EXISTS,LEFT_IMP_EXISTS_THM;
   end;
  qed by EQ_TAC,3`;;

thm `;
  !s. INFINITE s ==> ?x:A. x IN s
  proof
    let s be A->bool;
    assume INFINITE s;
    ~(s = {}) by INFINITE_NONEMPTY;
    consider x such that
      ~(x IN s <=> x IN {}) [1] by EXTENSION;
    take x;
    ~(x IN {}) by NOT_IN_EMPTY;
  qed by 1`;;

let NOT_EVEN = thm `;
  !n. ~EVEN n <=> ODD n
  proof
    ~EVEN 0 <=> ODD 0 [1] by EVEN,ODD;
    !n. (~EVEN n <=> ODD n) ==> (~EVEN (SUC n) <=> ODD (SUC n))
      by EVEN,ODD;
  qed by 1,INDUCT_TAC`;;

