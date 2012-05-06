(* ======== Robbins Conjecture proof from John ============================= *)

hide_constant "+";;
horizon := 0;;
timeout := 2;; (* John apparently has a faster computer :-) *)

let ROBBINS = thm `;
  
  let (+) be A->A->A;
  let n be A->A;
  
  assume !x y. x+y = y+x [COM];
  assume !x y z. x+(y+z) = (x+y)+z [ASS];
  assume !a b. n(n(a+b)+n(a+n(b))) = a [ROB];
  
  consider x such that x:A = x;
  
  set u = n(x+n(x)) [U];
  set d = x+u [D];
  set c = x+x+x+u [C];
  set j = n(c+d) [J];
  set e = u+n(x+x)+n(c) [E];
  
  n(u+n(x+x)) = x [0]
  proof n(u+n(x+x))
      = n(n(x+n(x))+n(x+x)) by U;
     .= x by ROB,COM;
  qed by -;
  
  n(x+u+n(x+u+n(x+x)+n(c))) = n(c) [1]
  proof n(x+u+n(x+u+n(x+x)+n(c)))
      = n((x+u)+n(x+u+n(x+x)+n(c))) by ASS,COM;
     .= n(n(n((x+u)+x+x)+n((x+u)+n(x+x)))+n(x+u+n(x+x)+n(c))) by ROB;
     .= n(n(n(x+u+x+x)+n(x+u+n(x+x)))+n(x+u+n(x+x)+n(c))) by ASS;
     .= n(n(n(x+x+x+u)+n(x+u+n(x+x)))+n(x+u+n(x+x)+n(c))) by ASS,COM; // slow
     .= n(n(n(c)+n(x+u+n(x+x)))+n(n(c)+x+u+n(x+x))) by ASS,COM,C;
     .= n(c) by ROB,ASS,COM;
  qed by -;                                   
                                  
  n(u+n(c)) = x [2]     
  proof n(u+n(c))
      = n(u+n(x+x+u+x)) by C,ASS,COM;                                           
     .= n(u+n(x+x+u+n(u+n(x+x)))) by 0;                    
     .= n(n(n(u+x+x)+n(u+n(x+x)))+n(x+x+u+n(u+n(x+x)))) by ROB;
     .= n(n(x+x+u+n(u+n(x+x)))+n(n(u+x+x)+n(u+n(x+x)))) by COM;
     .= n(n((x+x+u)+n(u+n(x+x)))+n(n(u+x+x)+n(u+n(x+x)))) by ASS;
     .= n(n(n(u+n(x+x))+u+x+x)+n(n(u+n(x+x))+n(u+x+x))) by ASS,COM;
     .= n(u+n(x+x)) by ROB;
     .= x by 0;
  qed by -;
  
  n(j+u) = x [3]
  proof n(j+u)
      = n(n(x+c+u)+u) by J,D,COM,ASS;
     .= n(n(x+c+u)+n(n(u+c)+n(u+n(c)))) by ROB;
     .= n(n(x+c+u)+n(x+n(c+u))) by 2,COM;
     .= x by ROB;
  qed by -;
  
  n(x+n(x+n(x+x)+u+n(c))) = n(x+x) [4]
  proof n(x+n(x+n(x+x)+u+n(c)))
      = n(n(n(x+n(u+n(c)))+n(x+u+n(c)))+n(x+n(x+x)+u+n(c)))
            by ROB,ASS,COM;
     .= n(n(n(x+x)+n(x+u+n(c)))+n(n(x+x)+x+u+n(c))) by 2,ASS,COM;
     .= n(n(n(x+x)+x+u+n(c))+n(n(x+x)+n(x+u+n(c)))) by ASS,COM;
     .= n(x+x) by ROB,COM;
  qed by -;
  
  n(x+n(c)) = u [5]
  proof n(x+n(c))
      = n(x+n(x+u+n(x+u+n(x+x)+n(c)))) by 1;
     .= n(n(u+n(x+x))+n(x+u+n(x+u+n(x+x)+n(c)))) by 0;
     .= n(n(u+n(x+x))+n(u+x+n(x+e))) by E,COM,ASS;
     .= n(n(u+n(x+n(x+n(x+x)+u+n(c))))+n(u+x+n(x+e))) by 4;
     .= n(n(u+n(x+n(x+(u+n(c))+n(x+x))))+n(u+x+n(x+e))) by COM;
     .= n(n(u+n(x+n(x+u+n(c)+n(x+x))))+n(u+x+n(x+e))) by ASS;
     .= n(n(u+n(x+n(x+u+n(x+x)+n(c))))+n(u+x+n(x+e))) by COM;
     .= n(n(u+n(x+n(x+e)))+n(u+x+n(x+e))) by E;
     .= u by ROB,COM;
  qed by -;
  
  n(j+x) = u [6]
  proof n(j+x)
      = n(j+n(n(x+c)+n(x+n(c)))) by ROB;
     .= n(j+n(n(x+c)+u)) by 5;
     .= n(n(u+x+c)+n(u+n(x+c))) by J,D,COM,ASS;
     .= u by ROB;
  qed by -;
  
  n(c+d) = n(c)
  proof n(c+d)
      = j by J;
     .= n(n(j+n(x+n(c)))+n(j+x+n(c))) by ROB,COM;
     .= n(n(j+u)+n(j+x+n(c))) by 5;
     .= n(x+n(j+x+n(c))) by 3;
     .= n(n(n(c)+u)+n(n(c)+j+x)) by 2,COM,ASS;
     .= n(n(n(c)+n(j+x))+n(n(c)+j+x)) by 6;
     .= n(c) by ROB,COM;
  qed by -;
  
  thus ?c d. n(c+d) = n(c) by -`;;

timeout := 1;;

(* ======== REWRITE version ================================================ *)

let old_default_prover = !default_prover;;
default_prover := "REWRITE_TAC",REWRITE_TAC;;

let ROBBINS = thm `;
  
  let (+) be A->A->A;
  let n be A->A;
  
  assume !x y. x+y = y+x [COM];
  assume !x y z. x+(y+z) = (x+y)+z [ASS];
  assume !a b. n(n(a+b)+n(a+n(b))) = a [ROB];
  
  !x y z. x+y = y+x /\ (x+y)+z = x+(y+z) /\ x+(y+z) = y+(x+z) [AC]
    by MESON_TAC,COM,ASS;
  
  consider x such that x:A = x;
  
  set u = n(x+n(x)) [U];
  set d = x+u [D];
  set c = x+x+x+u [C];
  set j = n(c+d) [J];
  set e = u+n(x+x)+n(c) [E];
  
  n(u+n(x+x)) = x [0]
  proof n(u+n(x+x))
      = n(n(x+x)+n(x+n(x))) by U,AC;
     .= x by ROB;
  qed by -;
  
  n(x+u+n(x+u+n(x+x)+n(c))) = n(c) [1]
  proof n(x+u+n(x+u+n(x+x)+n(c)))
      = n((x+u)+n(x+u+n(x+x)+n(c))) by AC;
     .= n(n(n((x+u)+x+x)+n((x+u)+n(x+x)))+n(x+u+n(x+x)+n(c))) by ROB;
     .= n(n(n(c)+x+u+n(x+x))+n(n(c)+n(x+u+n(x+x)))) by C,AC;
     .= n(c) by ROB;
  qed by -;
  
  n(u+n(c)) = x [2]
  proof n(u+n(c))
      = n(u+n(x+x+u+n(u+n(x+x)))) by 0,C,AC;
     .= n(n(n(u+x+x)+n(u+n(x+x)))+n(x+x+u+n(u+n(x+x)))) by ROB;
     .= n(n(n(u+n(x+x))+u+x+x)+n(n(u+n(x+x))+n(u+x+x))) by AC;
     .= n(u+n(x+x)) by ROB;
     .= x by 0;
  qed by -;
  
  n(j+u) = x [3]
  proof n(j+u)
      = n(n(x+c+u)+u) by J,D,AC;
     .= n(n(x+c+u)+n(n(u+c)+n(u+n(c)))) by ROB;
     .= n(n(x+c+u)+n(x+n(c+u))) by 2,AC;
     .= x by ROB;
  qed by -;
  
  n(x+n(x+n(x+x)+u+n(c))) = n(x+x) [4]
  proof n(x+n(x+n(x+x)+u+n(c)))
      = n(n(n(x+u+n(c))+n(x+n(u+n(c))))+n(x+n(x+x)+u+n(c))) by ROB;
     .= n(n(n(x+x)+x+u+n(c))+n(n(x+x)+n(x+u+n(c)))) by 2,AC;
     .= n(x+x) by ROB;
  qed by -;
  
  n(x+n(c)) = u [5]
  proof n(x+n(c))
      = n(n(u+n(x+x))+n(x+u+n(x+u+n(x+x)+n(c)))) by 0,1;
     .= n(n(u+n(x+n(x+n(x+x)+u+n(c))))+n(u+x+n(x+e))) by 4,E,AC;
     .= n(n(u+x+n(x+e))+n(u+n(x+n(x+e)))) by E,AC;
     .= u by ROB;
  qed by -;
  
  n(j+x) = u [6]
  proof n(j+x)
      = n(j+n(n(x+c)+n(x+n(c)))) by ROB;
     .= n(n(u+x+c)+n(u+n(x+c))) by 5,J,D,AC;
     .= u by ROB;
  qed by -;
  
  n(c+d) = n(c)
  proof n(c+d)
      = j by J;
     .= n(n(j+x+n(c))+n(j+n(x+n(c)))) by ROB;
     .= n(n(u+n(c))+n(j+x+n(c))) by 2,3,5,AC;
     .= n(n(n(c)+j+x)+n(n(c)+n(j+x))) by 6,AC;
     .= n(c) by ROB;
  qed by -;
  
  thus ?c d. n(c+d) = n(c) by MESON_TAC,-`;;

unhide_constant "+";;
default_prover := old_default_prover;;

