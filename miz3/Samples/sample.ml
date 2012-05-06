horizon := 1;;

thm `;
let R be num->num->bool;
assume !x. R x x [1];
assume !x y z. R x y /\ R y z ==> R x z [2];
thus (!m n. m <= n ==> R m n) <=> (!n. R n (SUC n))
proof
 now [3] // back direction first
  assume !n. R n (SUC n);
  let m n be num;
  !d. R m (m + d) ==> R m (m + SUC d) [4] by 2,ADD_CLAUSES;
  R m (m + 0) by 1,ADD_CLAUSES;
  !d. R m (m + d) by 4,INDUCT_TAC;
  thus m <= n ==> R m n by LE_EXISTS;
 end;
 !n. n <= SUC n;
qed by 3`;;

