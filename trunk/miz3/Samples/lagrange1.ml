needs "Library/prime.ml";;

parse_as_infix("**",(20,"right"));;

let group = new_definition
  `group(g,(**),i,(e:A)) <=>
    (e IN g) /\ (!x. x IN g ==> i(x) IN g) /\
    (!x y. x IN g /\ y IN g ==> x**y IN g) /\
    (!x y z. x IN g /\ y IN g /\ z IN g ==> x**(y**z) = (x**y)**z) /\
    (!x. x IN g ==> x**e = x /\ e**x = x) /\
    (!x. x IN g ==> x**i(x) = e /\ i(x)**x = e)`;;

let subgroup = new_definition
  `subgroup h (g,(**),i,(e:A)) <=> h SUBSET g /\ group(h,(**),i,e)`;;

(* ======== translation of John's proof ==================================== *)

horizon := 1;;

let GROUP_LAGRANGE_COSETS = thm `;
  !g h (**) i e.
       group(g,(**),i,e:A) /\ subgroup h (g,(**),i,e) /\ FINITE g
       ==> ?q. CARD g = CARD q * CARD h /\
               !b. b IN g ==> ?a x. a IN q /\ x IN h /\ b = a**x
proof exec REWRITE_TAC[group; subgroup; SUBSET];
  let g h be A->bool;
  let (**) be A->A->A;
  let i be A->A;
  let e be A;
  assume e IN g;
  assume !x. x IN g ==> i(x) IN g [1];
  assume !x y. x IN g /\ y IN g ==> x**y IN g [2];
  assume !x y z. x IN g /\ y IN g /\ z IN g
                 ==> x**(y**z) = (x**y)**z [3];
  assume !x. x IN g ==> x**e = x /\ e**x = x [4];
  assume !x. x IN g ==> x**i(x) = e /\ i(x)**x = e [5];
  assume !x. x IN h ==> x IN g [6];
  assume e IN h [7];
  assume !x. x IN h ==> i(x) IN h [8];
  assume !x y. x IN h /\ y IN h ==> x**y IN h [9];
  assume !x y z. x IN h /\ y IN h /\ z IN h
                 ==> x**(y**z) = (x**y)**z;
  assume !x. x IN h ==> x**e = x /\ e**x = x [10];
  assume !x. x IN h ==> x**i(x) = e /\ i(x)**x = e [11];
  assume FINITE g [12];
  set coset = \a. {b | b IN g /\ ?x. x IN h /\ b = a**x} [coset];
  !a. coset a = {b' | b' IN g /\ ?x. x IN h /\ b' = a**x} [13];
  !a. a IN g ==> a IN coset a [14]
  proof let a be A;
    assume a IN g [15];
    ?x. x IN h /\ a = a**x by 4,7;
  qed by SIMP_TAC,13,15,IN_ELIM_THM;
  FINITE h [16] by 6,12,FINITE_SUBSET,SUBSET;
  !a. FINITE (coset a)
  proof let a be A;
    ?t. FINITE t /\ coset a SUBSET t
    proof take g;
    qed by SIMP_TAC,12,13,IN_ELIM_THM,SUBSET;
  qed by MATCH_MP_TAC,FINITE_SUBSET;
  !a x y. a IN g /\ x IN g /\ y IN g /\ a**x = a**y ==> x = y [17]
  proof let a x y be A;
    assume a IN g /\ x IN g /\ y IN g /\ a**x = a**y [18];
    (i(a)**a)**x = (i(a)**a)**y by 1,3;
    e**x = e**y by 5,18;
  qed by 4,18;
  !a. a IN g ==> CARD (coset a) = CARD h
  proof let a be A;
    assume a IN g [19];
    coset a = IMAGE (\x. a**x) h [20]
    proof
      !x. x IN g /\ (?x'. x' IN h /\ x = a**x') <=>
          ?x'. x = a**x' /\ x' IN h by 2,6;
    qed by REWRITE_TAC,13,EXTENSION,IN_IMAGE,IN_ELIM_THM;
    (!x y. x IN h /\ y IN h /\ a**x = a**y ==> x = y) /\ FINITE h
      by 6,16,17,19;
    CARD (IMAGE (\x. a**x) h) = CARD h by MATCH_MP_TAC,CARD_IMAGE_INJ;
  qed by 20;
  !x y. x IN g /\ y IN g ==> i(x**y) = i(y)**i(x) [21]
  proof let x y be A;
    assume x IN g /\ y IN g [22];
    ?a. a IN g /\ i(x**y) IN g /\ i(y)**i(x) IN g /\
        a**i(x**y) = a**i(y)**i(x)
    proof take x**y;
      e = x**(y**i(y))**i(x) by 1,4,5,22;
        .= ((x**y)**i(y))**i(x) by 1,2,3,22;
    qed by SIMP_TAC,1,2,3,5,22;
  qed by 17;
  !x. x IN g ==> i(i(x)) = x [23]
  proof let x be A;
    assume x IN g;
    ?a. a IN g /\ i(i(x)) IN g /\ x IN g /\ a**i(i(x)) = a**x
    proof take i(x);
    qed by 1,5;
  qed by MATCH_MP_TAC,17;
  !a b. a IN g /\ b IN g
        ==> coset a = coset b \/ coset a INTER coset b = {}
  proof let a b be A;
    assume a IN g /\ b IN g [24];
    cases;
    suppose i(b)**a IN h [25];
      now let x be A;
        !x. x IN h ==> b**(i(b)**a)**x = a**x /\ a**i(i(b)**a)**x = b**x
          by SIMP_TAC,1,3,4,5,6,21,23,24;
        thus x IN g /\ (?x'. x' IN h /\ x = a**x') <=>
             x IN g /\ (?x'. x' IN h /\ x = b**x') by 8,9,25;
      end;
      coset a = coset b by REWRITE_TAC,13,EXTENSION,IN_ELIM_THM;
    qed;
    suppose ~(i(b)**a IN h) [26];
      now let x be A;
        assume x IN g /\ (?y. y IN h /\ x = a**y) /\ (?z. z IN h /\ x = b**z);
        consider y z such that y IN h /\ x = a**y /\ z IN h /\ x = b**z [27];
        (i(b)**a)**y = i(b)**a**y by 1,3,6,24,27;
          .= i(b)**b**z by 27;
          .= e**z by 1,3,5,6,24,27;
          .= z by 10,27;
        z**i(y) = ((i(b)**a)**y)**i(y);
          .= (i(b)**a)**y**i(y) by 1,2,3,5,6,24,27;
          .= (i(b)**a)**e by 11,27;
          .= i(b)**a by 1,2,4,24;
        thus F by 8,9,26,27;
      end;
      !x. ~((x IN g /\ ?y. y IN h /\ x = a**y) /\
            (x IN g /\ ?z. z IN h /\ x = b**z));
      coset a INTER coset b = {}
        by REWRITE_TAC,13,EXTENSION,NOT_IN_EMPTY,IN_INTER,IN_ELIM_THM;
    qed;
  end;
  set q = {c | ?a. a IN g /\ c = (@)(coset a)} [q] [28]; take q;
  !b. b IN g ==> ?a x. a IN q /\ x IN h /\ b = a**x [29]
  proof let b be A;
    assume b IN g [30];
    set C = (@)(coset b) [C] [31]; take C;
    (@)(coset b) IN {c | ?a. a IN g /\ c = (@)(coset a)} by 30;
    thus C IN q by q,C;
    C IN coset b by 14,30,C,IN,SELECT_AX;
    C IN {b' | b' IN g /\ ?x. x IN h /\ b' = b**x} by 13;
    consider c such that
      C IN g /\ c IN h /\ C = b**c [32];
    take i(c);
    (b**c)**i(c) = b**c**i(c) by 1,3,6,30;
      .= b by 1,4,5,6,30,32;
  qed by 8,32;
  !a b. a IN g /\ b IN g /\ a IN coset b ==> b IN coset a [33]
  proof let a b be A;
    a IN g /\ b IN g /\ a IN g /\ (?x. x IN h /\ a = b**x)
    ==> b IN g /\ (?x. x IN h /\ b = a**x)
    proof
      assume a IN g /\ b IN g /\ a IN g /\ ?x. x IN h /\ a = b**x [34];
      thus b IN g;
      consider c such that c IN h /\ a = b**c by 34;
      take i(c);
    qed by 3,4,6,8,11,34;
  qed by REWRITE_TAC,13,IN_ELIM_THM;
  !a b c. a IN coset b /\ b IN coset c /\ c IN g ==> a IN coset c [35]
  proof let a b c be A;
    now assume (a IN g /\ ?x. x IN h /\ a = b**x) /\
               (b IN g /\ ?x. x IN h /\ b = c**x) /\ c IN g [36];
      consider x x' such that x IN h /\ a = b**x /\ x' IN h /\ b = c**x';
      thus a IN g /\ ?x. x IN h /\ a = c**x by 3,6,9,36;
    end;
  qed by REWRITE_TAC,13,IN_ELIM_THM;
  !a b. a IN coset b ==> a IN g [37]
  proof let a b be A;
    a IN g /\ (?x. x IN h /\ a = b**x) ==> a IN g;
  qed by REWRITE_TAC,13,IN_ELIM_THM;
  !a b. a IN coset b /\ b IN g ==> coset a = coset b [38]
    by 33,35,37,EXTENSION;
  !a. a IN g ==> (@)(coset a) IN coset a [39] by 14,IN,SELECT_AX;
  !a. a IN q ==> a IN g [40]
  proof let a be A; assume a IN q;
    a IN {c | ?a. a IN g /\ c = (@)(coset a)} by q;
    consider a' such that a' IN g /\ a = (@)(coset a');
  qed by 37,39;
  !a x a' x'. a IN q /\ a' IN q /\ x IN h /\ x' IN h /\ a'**x' = a**x
              ==> a' = a /\ x' = x [41]
  proof let a x a' x' be A;
    assume a IN q /\ a' IN q /\ x IN h /\ x' IN h /\ a'**x' = a**x [42];
    a IN {c | ?a. a IN g /\ c = (@)(coset a)} /\
    a' IN {c | ?a. a IN g /\ c = (@)(coset a)} by q;
    consider a1 a2 such that
      a1 IN g /\ a = (@)(coset a1) /\ a2 IN g /\ a' = (@)(coset a2) [43];
    a IN g /\ a' IN g [44] by 37,39;
    coset a = coset a1 /\ coset a' = coset a2 by 38,39,43;
    a = (@)(coset a) /\ a' = (@)(coset a') [45] by 43;
    ?x. x IN h /\ a' = a**x
    proof take x**i(x');
      thus x**i(x') IN h by 8,9,42;
      a' = a'**x'**i(x') by 4,5,6,42,44;
        .= (a**x)**i(x') by 1,2,3,6,42,44;
    qed by 1,2,3,6,42,44;
    a' IN coset a by REWRITE_TAC,13,44,IN_ELIM_THM;
    coset a = coset a' by 38,44;
  qed by 6,17,42,44,45;
  g = IMAGE (\(a,x). a**x) {(a,x) | a IN q /\ x IN h}
  proof
    !x. x IN g <=> ?p1 p2. (x = p1**p2 /\ p1 IN q) /\ p2 IN h by 2,6,29,40;
  qed by REWRITE_TAC,EXTENSION,IN_IMAGE,IN_ELIM_THM,EXISTS_PAIR_THM,PAIR_EQ,
         CONJ_ASSOC,ONCE_REWRITE_RULE[CONJ_SYM] UNWIND_THM1;
  CARD g = CARD (IMAGE (\(a,x). a**x) {(a,x) | a IN q /\ x IN h}) [46];
    .= CARD {(a,x) | a IN q /\ x IN h}
  proof
    !x y. x IN {(a,x) | a IN q /\ x IN h} /\
          y IN {(a,x) | a IN q /\ x IN h} /\
          (\(a,x). a**x) x = (\(a,x). a**x) y
          ==> x = y [47]
    proof
      !p1 p2 p1' p2'. (?a x. (a IN q /\ x IN h) /\ p1 = a /\ p2 = x) /\
                      (?a x. (a IN q /\ x IN h) /\ p1' = a /\ p2' = x) /\
                      p1**p2 = p1'**p2'
                      ==> p1 = p1' /\ p2 = p2' by 41;
    qed by REWRITE_TAC,FORALL_PAIR_THM,IN_ELIM_THM,PAIR_EQ;
    FINITE q /\ FINITE h by 6,12,40,FINITE_SUBSET,SUBSET;
    FINITE {(a,x) | a IN q /\ x IN h} by FINITE_PRODUCT;
  qed by MATCH_MP_TAC CARD_IMAGE_INJ,47;
    .= CARD q * CARD h by 6,12,40,46,CARD_PRODUCT,FINITE_SUBSET,SUBSET;
qed by 29`;;

let GROUP_LAGRANGE = thm `;
  !g h (**) i e.
       group (g,( ** ),i,e:A) /\ subgroup h (g,(**),i,e) /\ FINITE g
       ==> CARD h divides CARD g
  by GROUP_LAGRANGE_COSETS,DIVIDES_LMUL,DIVIDES_REFL`;;

(* ======== and formal proof sketch derived from this translation ========== *)

horizon := -1;;

let GROUP_LAGRANGE_COSETS_SKETCH = ref None;;

GROUP_LAGRANGE_COSETS_SKETCH := Some `;
  !g h (**) i e.
       group(g,(**),i,e:A) /\ subgroup h (g,(**),i,e) /\ FINITE g
       ==> ?q. CARD g = CARD q * CARD h /\
               !b. b IN g ==> ?a x. a IN q /\ x IN h /\ b = a**x
proof exec REWRITE_TAC[group; subgroup; SUBSET];
  let g h be A->bool;
  let (**) be A->A->A;
  let i be A->A;
  let e be A;
  assume e IN g;
  assume !x. x IN g ==> i(x) IN g;
  assume !x y. x IN g /\ y IN g ==> x**y IN g;
  assume !x y z. x IN g /\ y IN g /\ z IN g
                 ==> x**(y**z) = (x**y)**z;
  assume !x. x IN g ==> x**e = x /\ e**x = x;
  assume !x. x IN g ==> x**i(x) = e /\ i(x)**x = e;
  assume !x. x IN h ==> x IN g;
  assume e IN h;
  assume !x. x IN h ==> i(x) IN h;
  assume !x y. x IN h /\ y IN h ==> x**y IN h;
  assume !x y z. x IN h /\ y IN h /\ z IN h
                 ==> x**(y**z) = (x**y)**z;
  assume !x. x IN h ==> x**e = x /\ e**x = x;
  assume !x. x IN h ==> x**i(x) = e /\ i(x)**x = e;
  assume FINITE g;
  set coset = \a. {b | b IN g /\ ?x. x IN h /\ b = a**x};
  !a. coset a = {b' | b' IN g /\ ?x. x IN h /\ b' = a**x};
  !a. a IN g ==> a IN coset a
  proof let a be A;
    assume a IN g;
    ?x. x IN h /\ a = a**x;
  qed;
  FINITE h;
::        #1
:: 1: inference error
  !a. FINITE (coset a)
  proof let a be A;
    ?t. FINITE t /\ coset a SUBSET t
    proof take g;
    qed;
::     #2
:: 2: inference time-out
  qed;
::   #2
  !a x y. a IN g /\ x IN g /\ y IN g /\ a**x = a**y ==> x = y
  proof let a x y be A;
    assume a IN g /\ x IN g /\ y IN g /\ a**x = a**y;
    (i(a)**a)**x = (i(a)**a)**y;
    e**x = e**y;
::             #2
  qed;
  !a. a IN g ==> CARD (coset a) = CARD h
  proof let a be A;
    assume a IN g;
    coset a = IMAGE (\x. a**x) h
    proof
      !x. x IN g /\ (?x'. x' IN h /\ x = a**x') <=>
          ?x'. x = a**x' /\ x' IN h;
    qed;
::     #2
    (!x y. x IN h /\ y IN h /\ a**x = a**y ==> x = y) /\ FINITE h;
    CARD (IMAGE (\x. a**x) h) = CARD h;
::                                    #2
  qed;
  !x y. x IN g /\ y IN g ==> i(x**y) = i(y)**i(x)
  proof let x y be A;
    assume x IN g /\ y IN g;
    ?a. a IN g /\ i(x**y) IN g /\ i(y)**i(x) IN g /\
        a**i(x**y) = a**i(y)**i(x)
    proof take x**y;
      e = x**(y**i(y))**i(x);
::                          #2
        .= ((x**y)**i(y))**i(x);
::                             #2
    qed;
  qed;
  !x. x IN g ==> i(i(x)) = x
  proof let x be A;
    assume x IN g;
    ?a. a IN g /\ i(i(x)) IN g /\ x IN g /\ a**i(i(x)) = a**x
    proof take i(x);
    qed;
  qed;
  !a b. a IN g /\ b IN g
        ==> coset a = coset b \/ coset a INTER coset b = {}
  proof let a b be A;
    assume a IN g /\ b IN g;
    cases;
    suppose i(b)**a IN h;
      now let x be A;
        !x. x IN h ==> b**(i(b)**a)**x = a**x /\ a**i(i(b)**a)**x = b**x;
::                                                                      #2
        thus x IN g /\ (?x'. x' IN h /\ x = a**x') <=>
             x IN g /\ (?x'. x' IN h /\ x = b**x');
::                                                #2
      end;
      coset a = coset b;
::                     #2
    qed;
    suppose ~(i(b)**a IN h);
      now let x be A;
        assume x IN g /\ (?y. y IN h /\ x = a**y) /\ (?z. z IN h /\ x = b**z);
        consider y z such that y IN h /\ x = a**y /\ z IN h /\ x = b**z;
        (i(b)**a)**y = i(b)**a**y;
          .= i(b)**b**z;
          .= e**z;
::               #2
          .= z;
        z**i(y) = ((i(b)**a)**y)**i(y);
          .= (i(b)**a)**y**i(y);
::                             #2
          .= (i(b)**a)**e;
          .= i(b)**a;
::                  #2
        thus F;
::            #2
      end;
      !x. ~((x IN g /\ ?y. y IN h /\ x = a**y) /\
            (x IN g /\ ?z. z IN h /\ x = b**z));
      coset a INTER coset b = {};
::                              #2
    qed;
  end;
  set q = {c | ?a. a IN g /\ c = (@)(coset a)};
  take q;
  !b. b IN g ==> ?a x. a IN q /\ x IN h /\ b = a**x
  proof let b be A;
    assume b IN g;
    set C = (@)(coset b);
    take C;
    (@)(coset b) IN {c | ?a. a IN g /\ c = (@)(coset a)};
    thus C IN q;
    C IN coset b;
::              #2
    C IN {b' | b' IN g /\ ?x. x IN h /\ b' = b**x};
    consider c such that
      C IN g /\ c IN h /\ C = b**c;
    take i(c);
    (b**c)**i(c) = b**c**i(c);
      .= b;
  qed;
  !a b. a IN g /\ b IN g /\ a IN coset b ==> b IN coset a
  proof let a b be A;
    a IN g /\ b IN g /\ a IN g /\ (?x. x IN h /\ a = b**x)
    ==> b IN g /\ (?x. x IN h /\ b = a**x)
    proof
      assume a IN g /\ b IN g /\ a IN g /\ ?x. x IN h /\ a = b**x;
      thus b IN g;
      consider c such that c IN h /\ a = b**c;
      take i(c);
    qed;
::     #2
  qed;
  !a b c. a IN coset b /\ b IN coset c /\ c IN g ==> a IN coset c
  proof let a b c be A;
    now assume (a IN g /\ ?x. x IN h /\ a = b**x) /\
               (b IN g /\ ?x. x IN h /\ b = c**x) /\ c IN g;
      consider x x' such that x IN h /\ a = b**x /\ x' IN h /\ b = c**x';
      thus a IN g /\ ?x. x IN h /\ a = c**x;
::                                         #2
    end;
  qed;
::   #2
  !a b. a IN coset b ==> a IN g
  proof let a b be A;
    a IN g /\ (?x. x IN h /\ a = b**x) ==> a IN g;
  qed;
  !a b. a IN coset b /\ b IN g ==> coset a = coset b;
::                                                  #2
  !a. a IN g ==> (@)(coset a) IN coset a;
::                                      #2
  !a. a IN q ==> a IN g
  proof let a be A;
    assume a IN q;
    a IN {c | ?a. a IN g /\ c = (@)(coset a)};
    consider a' such that a' IN g /\ a = (@)(coset a');
  qed;
  !a x a' x'. a IN q /\ a' IN q /\ x IN h /\ x' IN h /\ a'**x' = a**x
              ==> a' = a /\ x' = x
  proof let a x a' x' be A;
    assume a IN q /\ a' IN q /\ x IN h /\ x' IN h /\ a'**x' = a**x;
    a IN {c | ?a. a IN g /\ c = (@)(coset a)} /\
    a' IN {c | ?a. a IN g /\ c = (@)(coset a)};
    consider a1 a2 such that
      a1 IN g /\ a = (@)(coset a1) /\ a2 IN g /\ a' = (@)(coset a2);
::                                                                 #2
    a IN g /\ a' IN g;
    coset a = coset a1 /\ coset a' = coset a2;
::                                           #2
    a = (@)(coset a) /\ a' = (@)(coset a');
    ?x. x IN h /\ a' = a**x
    proof take x**i(x');
      thus x**i(x') IN h;
::                      #2
      a' = a'**x'**i(x');
::                      #2
        .= (a**x)**i(x');
::                      #2
    qed;
::     #2
    a' IN coset a;
::               #2
    coset a = coset a';
  qed;
::   #2
  g = IMAGE (\(a,x). a**x) {(a,x) | a IN q /\ x IN h}
  proof
    !x. x IN g <=> ?p1 p2. (x = p1**p2 /\ p1 IN q) /\ p2 IN h;
::                                                           #2
  qed;
::   #2
  CARD g = CARD (IMAGE (\(a,x). a**x) {(a,x) | a IN q /\ x IN h});
    .= CARD {(a,x) | a IN q /\ x IN h}
  proof
    !x y. x IN {(a,x) | a IN q /\ x IN h} /\
          y IN {(a,x) | a IN q /\ x IN h} /\
          (\(a,x). a**x) x = (\(a,x). a**x) y
          ==> x = y
    proof
      !p1 p2 p1' p2'. (?a x. (a IN q /\ x IN h) /\ p1 = a /\ p2 = x) /\
                      (?a x. (a IN q /\ x IN h) /\ p1' = a /\ p2' = x) /\
                      p1**p2 = p1'**p2'
                      ==> p1 = p1' /\ p2 = p2';
    qed;
::     #2
    FINITE q /\ FINITE h;
::                      #2
    FINITE {(a,x) | a IN q /\ x IN h};
::                                   #2
  qed;
::   #2
    .= CARD q * CARD h;
::                    #2
qed`;;

