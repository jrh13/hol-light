needs "Library/prime.ml";;

let group = new_definition
  `group(g,(**),i,(e:A)) <=>
    (e IN g) /\ (!x. x IN g ==> i(x) IN g) /\
    (!x y. x IN g /\ y IN g ==> x**y IN g) /\
    (!x y z. x IN g /\ y IN g /\ z IN g ==> x**(y**z) = (x**y)**z) /\
    (!x. x IN g ==> x**e = x /\ e**x = x) /\
    (!x. x IN g ==> x**i(x) = e /\ i(x)**x = e)`;;

let subgroup = new_definition
  `subgroup h (g,(**),i,(e:A)) <=> h SUBSET g /\ group(h,(**),i,e)`;;

let bijection = new_definition
  `bijection f s t <=> ?g. (!x:A. x IN s ==> f x IN t /\ g (f x) = x) /\
                           (!y:B. y IN t ==> g y IN s /\ f (g y) = y)`;;

parse_as_infix("PARTITIONS",(12,"right"));;

let PARTITIONS = new_definition
  `X PARTITIONS s <=> UNIONS X = (s:A->bool) /\
                      !t u. t IN X /\ u IN X /\ ~(t = u) ==> t INTER u = {}`;;

parse_as_infix("**",(20,"left"));;
parse_as_infix("***",(20,"left"));;

horizon := -1;;

let LAGRANGE_SKETCH = ref None;;

LAGRANGE_SKETCH := Some `;
  let H G be A->bool; let (**) be A->A->A; let i be A->A; let e be A;
  assume FINITE H /\ group (H,(**),i,e:A) /\ subgroup G (H,(**),i,e);
  consider (***) such that !h G. h***G = {h**g | g IN G};
//
  now let a be A; assume a IN H; let b be A; assume b IN H;
    assume i(a)**b IN G;
    b***G = a**i(a)**b***G; .= a***(i(a)**b***G); thus .= a***G;
  end;
  !a b. a IN H /\ b IN H /\ ~(a***G = b***G) ==> a***G INTER b***G = {}
  proof let a be A; assume a IN H; let b be A; assume b IN H;
    now assume ~(a***G INTER b***G = {});
      consider g1 g2 such that g1 IN G /\ g2 IN G /\ a**g1 = b**g2;
      g1**i(g2) = i(a)**b;
      i(a)**b IN G;
      thus a***G = b***G;
    end;
  qed;
  !a. a IN H ==> a IN a***G
  proof let a be A; assume a IN H;
    a**e = a;
  qed;
  {a***G | a IN H} PARTITIONS H;
  !a b. a IN H /\ b IN H ==> CARD (a***G) = CARD (b***G)
  proof let a be A; assume a IN H; let b be A; assume b IN H;
    consider f such that !g. g IN G ==> f(a**g) = b**g;
    bijection f (a***G) (b***G);
  qed;
  set INDEX = CARD {a***G | a IN H};
  set N = CARD H; set n = CARD G; set j = INDEX;
  N = j*n;
  thus CARD G divides CARD H;
//
`;;

LAGRANGE_SKETCH := Some `;
  let H G be A->bool; let (**) be A->A->A; let i be A->A; let e be A;
  assume FINITE H /\ group (H,(**),i,e:A) /\ subgroup G (H,(**),i,e);
  consider (***) such that !h G. h***G = {h**g | g IN G};
::                                                      #2
:: 2: inference time-out
//
  now let a be A; assume a IN H; let b be A; assume b IN H;
    assume i(a)**b IN G;
    b***G = a**i(a)**b***G; .= a***(i(a)**b***G); thus .= a***G;
::                        #2                    #2             #2
  end;
  !a b. a IN H /\ b IN H /\ ~(a***G = b***G) ==> a***G INTER b***G = {}
  proof let a be A; assume a IN H; let b be A; assume b IN H;
    now assume ~(a***G INTER b***G = {});
      consider g1 g2 such that g1 IN G /\ g2 IN G /\ a**g1 = b**g2;
::                                                                #2
      g1**i(g2) = i(a)**b;
::                       #2
      i(a)**b IN G;
::                #2
      thus a***G = b***G;
    end;
  qed;
  !a. a IN H ==> a IN a***G
  proof let a be A; assume a IN H;
    a**e = a;
::          #1
:: 1: inference error
  qed;
::   #2
  {a***G | a IN H} PARTITIONS H;
::                             #2
  !a b. a IN H /\ b IN H ==> CARD (a***G) = CARD (b***G)
  proof let a be A; assume a IN H; let b be A; assume b IN H;
    consider f such that !g. g IN G ==> f(a**g) = b**g;
::                                                    #2
    bijection f (a***G) (b***G);
::                             #2
  qed;
::   #2
  set INDEX = CARD {a***G | a IN H};
  set N = CARD H; set n = CARD G; set j = INDEX;
  N = j*n;
::       #2
  thus CARD G divides CARD H;
::                          #2
//
`;;

horizon := 3;;

let UNIONS_FINITE = thm `;
  !s. FINITE (UNIONS s) <=>
      FINITE s /\ !t:A->bool. t IN s ==> FINITE t
proof
  let s be (A->bool)->bool;
  now assume FINITE (UNIONS s) [1];
    now let t be A->bool; assume t IN s;
      now let x be A; assume x IN t;
        ?t. t IN s /\ x IN t;
        thus x IN UNIONS s by ALL_TAC,UNIONS,IN_ELIM_THM;
      end;
      thus t IN {t | t SUBSET UNIONS s} by SUBSET,IN_ELIM_THM;
    end;
    s SUBSET {t | t SUBSET UNIONS s} by REWRITE_TAC,SUBSET;
    FINITE {t | t SUBSET UNIONS s} by 1,FINITE_POWERSET;
    thus FINITE s by FINITE_SUBSET;
  end;
qed by FINITE_UNIONS`;;

let CARD_UNIONS_EQUAL = thm `;
  !X s n. FINITE s /\ X PARTITIONS s /\ (!t:A->bool. t IN X ==> CARD t = n)
          ==> CARD s = (CARD X)*n
proof
  let X be (A->bool)->bool;
  let s be A->bool;
  let n be num;
  assume FINITE s;
  assume X PARTITIONS s [1];
  assume !t. t IN X ==> CARD t = n [2];
  FINITE (UNIONS X) by PARTITIONS;
  !t. t IN X ==> FINITE t [3] by UNIONS_FINITE;
  FINITE X [4] by UNIONS_FINITE;
  !t. t IN X ==> CARD t = (\t. n) t [5] by 2;
  !t u. t IN X /\ u IN X /\ ~(t = u) ==> t INTER u = {} by 1,PARTITIONS;
  CARD s = CARD (UNIONS X) by 1,PARTITIONS;
    .= nsum X CARD by 2,3,4,CARD_UNIONS;
    .= nsum X (\t. n) by 5,NSUM_EQ;
qed by 4,NSUM_CONST`;;

let BIJECTION_CARD_EQ = thm `;
  let f be A->B;
  let s be A->bool;
  let t be B->bool;
  assume FINITE s /\ bijection f s t [1];
  ?g. (!x. x IN s ==> f x IN t /\ g (f x) = x) /\
      (!y. y IN t ==> g y IN s /\ f (g y) = y)
    by REWRITE_TAC,-,GSYM bijection;
  thus CARD s = CARD t by -,1,BIJECTIONS_CARD_EQ`;;

horizon := 0;;

let LAGRANGE = thm `;
  let H G be A->bool;
  let (**) be A->A->A;
  let i be A->A;
  let e be A;
  assume FINITE H /\ group (H,(**),i,e) /\ subgroup G (H,(**),i,e) [1];
  (e IN H) /\ (!x. x IN H ==> i(x) IN H) /\
    (!x y. x IN H /\ y IN H ==> x**y IN H) /\
    (!x y z. x IN H /\ y IN H /\ z IN H ==> x**(y**z) = (x**y)**z) /\
    (!x. x IN H ==> x**e = x /\ e**x = x) /\
    (!x. x IN H ==> x**i(x) = e /\ i(x)**x = e) [2]
      by REWRITE_TAC,1,GSYM group;
  (G SUBSET H) /\ group (G,(**),i,e) [3] by 1,subgroup;
  !x. x IN G ==> x IN H [4] by -,SUBSET;
  FINITE G [5] by 3,1,FINITE_SUBSET;
  (e IN G) /\ (!x. x IN G ==> i(x) IN G) /\
    (!x y. x IN G /\ y IN G ==> x**y IN G) /\
    (!x y z. x IN G /\ y IN G /\ z IN G ==> x**(y**z) = (x**y)**z) /\
    (!x. x IN G ==> x**e = x /\ e**x = x) /\
    (!x. x IN G ==> x**i(x) = e /\ i(x)**x = e) [6]
      by REWRITE_TAC,3,GSYM group;
  set (***) = \h G. {h**g | g IN G} [7];
  !x h G. x IN h***G <=> ?g. g IN G /\ x = h**g [8] by ALL_TAC,-,IN_ELIM_THM;
  !h1 h2. h1 IN H /\ h2 IN H ==> (h1**h2)***G = h1***(h2***G) [9]
  proof
    let h1 h2 be A;
    assume h1 IN H /\ h2 IN H [10];
    now [11]
      let x be A;
      assume x IN (h1**h2)***G;
      consider g such that g IN G /\ x = (h1**h2)**g [12] by -,8;
      g IN H by -,4;
      x = h1**(h2**g) [13] by -,2,10,12;
      h2**g IN h2***G by 8,12;
      thus x IN h1***(h2***G) by -,13,8;
    end;
    now
      let x be A;
      assume x IN h1***(h2***G);
      consider y such that y IN h2***G /\ x = h1**y [14] by -,8;
      consider g such that g IN G /\ y = h2**g [15] by -,8;
      g IN H [16] by -,4;
      x = h1**(h2**g) by 14,15;
        .= (h1**h2)**g by -,2,10,14,16;
      thus x IN (h1**h2)***G by -,8,15;
    end;
  qed by -,11,EXTENSION;
  !g. g IN G ==> g***G = G [17]
  proof
    let g be A;
    assume g IN G [18];
    now [19]
      let x be A;
      assume x IN g***G;
      consider g' such that g' IN G /\ x = g**g' by -,8;
      thus x IN G by -,6,18;
    end;
    now
      let x be A;
      assume x IN G [20];
      x = g**i(g)**x by -,6,18;
        .= g**(i(g)**x) [21] by -,6,18,20;
      i(g)**x IN G by 6,18,20;
      thus x IN g***G by -,21,8;
    end;
  qed by -,19,EXTENSION;
//
  now [22]
    let a be A; assume a IN H [23];
    let b be A; assume b IN H [24];
    i(a)**b IN H [25] by 2,23,24;
    assume i(a)**b IN G [26];
    b***G = e**b***G by 2,24;
      .= a**i(a)**b***G by -,2,23;
      .= a**(i(a)**b)***G by -,2,23,24;
      .= a***(i(a)**b***G) by -,9,23,25;
    thus .= a***G by -,17,26;
  end;
  !a b. a IN H /\ b IN H /\ ~(a***G = b***G) ==> a***G INTER b***G = {} [27]
  proof
    let a be A; assume a IN H [28];
    let b be A; assume b IN H [29];
    now assume ~(a***G INTER b***G = {});
      consider x such that x IN a***G INTER b***G by -,MEMBER_NOT_EMPTY;
      x IN a***G /\ x IN b***G [30] by -,IN_INTER;
      consider g1 such that g1 IN G /\ x = a**g1 [31] by 8,30;
      consider g2 such that g2 IN G /\ x = b**g2 [32] by 8,30;
      g1 IN H /\ g2 IN H [33] by 4,31,32;
      a**g1 = b**g2 [34] by 31,32;
      g1**i(g2) = e**g1**i(g2) by 2,33;
        .= (i(a)**a)**g1**i(g2) by -,2,28;
        .= i(a)**(a**g1)**i(g2) by -,2,28,33;
        .= i(a)**(b**g2)**i(g2) by -,34;
        .= i(a)**(b**g2**i(g2)) by -,2,28,29,33;
        .= i(a)**(b**(g2**i(g2))) by -,2,29,33;
        .= i(a)**(b**e) by -,2,33;
        .= i(a)**b by -,2,29;
      i(a)**b IN G by -,6,31,32;
      thus a***G = b***G by -,22,28,29;
    end;
  qed by -,28,29;
  !a. a IN H ==> a IN a***G [35]
  proof
    let a be A; assume a IN H;
    a**e = a by -,2;
  qed by -,6,8;
  now
    now [36]
      let x be A;
      assume x IN UNIONS {a***G | a IN H};
      consider s such that s IN {a***G | a IN H} /\ x IN s [37]
        by -,IN_UNIONS;
      consider a such that a IN H /\ s = a***G [38] by -;
      consider g such that g IN G /\ x = a**g by -,8,37;
      thus x IN H by -,2,4,38;
    end;
    now
      let x be A;
      assume x IN H;
      x IN x***G /\ x***G IN {a***G | a IN H} by -,35;
      thus x IN UNIONS {a***G | a IN H} by -,IN_UNIONS;
    end;
    thus UNIONS {a***G | a IN H} = H by -,36,EXTENSION;
    let t u be A->bool;
    assume t IN {a***G | a IN H} /\ u IN {a***G | a IN H} /\ ~(t = u) [39];
    consider a b such that a IN H /\ t = a***G /\ b IN H /\ t = b***G by -;
    thus t INTER u = {} by -,27,39;
  end;
  {a***G | a IN H} PARTITIONS H [40] by REWRITE_TAC,-,PARTITIONS;
  !a b. a IN H /\ b IN H ==> CARD (a***G) = CARD (b***G) [41]
  proof
    let a be A; assume a IN H [42];
    let b be A; assume b IN H [43];
    set f = \x. b**(i(a)**x);
    set f' = \x. a**(i(b)**x);
    !g. g IN G ==> f(a**g) = b**g /\ f'(b**g) = a**g [44]
    proof
      let g be A; assume g IN G;
      g IN H [45] by -,4;
      f(a**g) = b**(i(a)**(a**g));
        .= b**(i(a)**a**g) by -,2,42,45;
        .= b**(e**g) by -,2,42;
        .= b**g [46] by -,2,45;
      f'(b**g) = a**(i(b)**(b**g));
        .= a**(i(b)**b**g) by -,2,43,45;
        .= a**(e**g) by -,2,43;
        .= a**g by -,2,45;
    qed by -,46;
    now
      take f';
      thus !x. x IN a***G ==> f x IN b***G /\ f' (f x) = x
      proof
        let x be A; assume x IN a***G;
        consider g such that g IN G /\ x = a**g [47] by -,8;
        f x = b**g by -,44;
      qed by -,8,44,47;
      thus !y. y IN b***G ==> f' y IN a***G /\ f (f' y) = y
      proof
        let y be A; assume y IN b***G;
        consider g such that g IN G /\ y = b**g [48] by -,8;
        f' y = a**g by -,44;
      qed by -,8,44,48;
    end;
    bijection f (a***G) (b***G) [49] by ALL_TAC,-,bijection;
    FINITE {a**g | g IN G} by SIMP_TAC,5,SIMPLE_IMAGE,FINITE_IMAGE;
  qed by -,7,49,BIJECTION_CARD_EQ;
  set INDEX = CARD {a***G | a IN H};
  now
    let t be A->bool;
    assume t IN {a***G | a IN H};
    consider a such that a IN H /\ t = a***G [50] by -;
    CARD t = CARD (a***G) by -;
      .= CARD (e***G) by -,2,41,50;
    thus .= CARD G by -,6,17;
  end;
  set N = CARD H;
  set n = CARD G;
  set j = INDEX;
  N = (CARD {a***G | a IN H})*(CARD G) by -,1,40,CARD_UNIONS_EQUAL;
    .= j*n by -;
  thus CARD G divides CARD H by -,divides,MULT_SYM;
//
`;;

parse_as_infix("**",(20,"right"));;
