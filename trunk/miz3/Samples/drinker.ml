horizon := 0;;

thm `;
  assume ?x:A. T [1];
  let P be A->bool;
  thus ?x. P x ==> !y. P y
  proof
    (?x. ~P x) \/ ~(?x. ~P x);  // LEM
    cases by -;                 // \/E
    suppose ?x. ~P x;
      consider x such that
        ~P x [2] by -;          // ?E
      take x;                   // ?I
      assume P x;               // ==>I
      F by 2,-;                 // ~E
    qed by -;                   // FE
    suppose ~(?x. ~P x) [3];
      consider x such that
        (\x:A. T) x by 1;       // ?E
      take x;                   // ?I
      assume P x;               // ==>I
      let y be A;               // !I
      P y \/ ~P y;              // LEM
      cases by -;               // \/E
      suppose P y;
      qed by -;                 //
      suppose ~P y;
        ?y. ~P y
        proof
          take y;               // ?I
        qed by -;               //
        F by 3,-;               // ~E
      qed by -;                 // FE
    end;
  end`;;

