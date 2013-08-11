(* ----------------------------------------------------------------- *)
(* HOL Light Hilbert geometry axiomatic proofs using miz3.           *)
(* ----------------------------------------------------------------- *)

(* High school students can learn rigorous axiomatic Geometry proofs,
   as in http://www.math.northwestern.edu/~richter/hilbert.pdf, using
   Hilbert's axioms, and code up their proofs in miz3 and HOL Light.
   Thanks to Bjørn Jahren, Miguel Lerma,Takuo Matsuoka, Stephen
   Wilson for advice on Hilbert's axioms, and especially Benjamin
   Kordesh, who carefully read much of the paper and the code.

   Formal proofs are given for the first 7 sections of the paper, the
   results cited there from Greenberg's book, and most of Euclid's
   book I propositions up to Proposition I.29, following Hartshorne,
   whose book seems the most exciting axiomatic geometry text.  A
   proof assistant is an valuable tool to help read it, as
   Hartshorne's proofs are often sketchy and even have gaps.

   M. Greenberg, Euclidean and non-Euclidean geometries, W. H. Freeman and Co., 1974.
   R. Hartshorne, Geometry, Euclid and Beyond, Undergraduate Texts in Math., Springer, 2000.

   Thanks to Mizar folks for their influential language, Freek
   Wiedijk, who wrote the miz3 port of Mizar to HOL Light, and
   especially John Harrison, who was extremely helpful and developed
   the framework for porting my axiomatic proofs to HOL Light.  *)

verbose := false;;
report_timing := false;;

horizon := 0;;
timeout := 150;;

new_type("point",0);;
new_type_abbrev("point_set",`:point->bool`);;
new_constant("Between",`:point->point->point->bool`);;
new_constant("Line",`:point_set->bool`);;
new_constant("===",`:(point->bool)->(point->bool)->bool`);;

parse_as_infix("cong",(12, "right"));;
parse_as_infix("same_side",(12, "right"));;
parse_as_infix("===",(12, "right"));;
parse_as_infix("<__",(12, "right"));;
parse_as_infix("<_ang",(12, "right"));;
parse_as_infix("suppl",(12, "right"));;
parse_as_infix("NOTIN",(11, "right"));;
parse_as_infix("parallel",(12, "right"));;

let NOTIN = new_definition
  `!a:A l:A->bool. a NOTIN l <=> ~(a IN l)`;;

let Interval_DEF = new_definition
  `! A B. open (A,B) = {X | Between A X B}`;;

let Collinear_DEF = new_definition
  `Collinear A B C  <=>
  ? l. Line l /\ A IN l /\ B IN l /\ C IN l`;;

let SameSide_DEF = new_definition
  `A,B same_side l  <=>
  Line l /\ ~ ? X. (X IN l) /\  X IN open (A,B)`;;

let Ray_DEF = new_definition
  `! A B. ray A B = {X | ~(A = B) /\ Collinear A B X /\ A NOTIN open (X,B)}`;;

let Ordered_DEF = new_definition
 `ordered A B C D  <=>
  B IN open (A,C) /\ B IN open (A,D) /\ C IN open (A,D) /\ C IN open (B,D)`;;

let InteriorAngle_DEF = new_definition
 `! A O B.  int_angle A O B =
    {P:point | ~Collinear A O B /\ ? a b.
               Line a /\ O IN a /\ A IN a /\ Line b /\ O IN b /\ B IN b /\
               P NOTIN a /\ P NOTIN b /\ P,B same_side a /\ P,A same_side b}`;;

let InteriorTriangle_DEF = new_definition
 `! A B C.  int_triangle A B C =
    {P | P IN int_angle A B C  /\
         P IN int_angle B C A  /\
         P IN int_angle C A B}`;;

let Tetralateral_DEF = new_definition
  `Tetralateral A B C D  <=>
  ~(A = B) /\ ~(A = C) /\ ~(A = D) /\ ~(B = C) /\ ~(B = D) /\ ~(C = D) /\
  ~Collinear A B C /\ ~Collinear B C D /\ ~Collinear C D A /\ ~Collinear D A B`;;

let Quadrilateral_DEF = new_definition
  `Quadrilateral A B C D  <=>
  Tetralateral A B C D /\
  open (A,B) INTER open (C,D) = {} /\
  open (B,C) INTER open (D,A) = {} `;;

let ConvexQuad_DEF = new_definition
  `ConvexQuadrilateral A B C D  <=>
  Quadrilateral A B C D /\
  A IN int_angle B C D /\ B IN int_angle C D A /\ C IN int_angle D A B /\ D IN int_angle A B C `;;

let Segment_DEF = new_definition
  `seg A B = {A, B} UNION open (A,B)`;;

let SEGMENT = new_definition
  `Segment s  <=>  ? A B. s = seg A B /\ ~(A = B)`;;

let SegmentOrdering_DEF = new_definition
 `s <__ t   <=>
  Segment s /\
  ? C D X. t = seg C D /\ X IN open (C,D) /\ s === seg C X`;;

let Angle_DEF = new_definition
 ` angle A O B = ray O A UNION ray O B `;;

let ANGLE = new_definition
 `Angle alpha  <=>  ? A O B. alpha = angle A O B /\ ~Collinear A O B`;;

let AngleOrdering_DEF = new_definition
 `alpha <_ang beta  <=>
  Angle alpha /\
  ? A O B G. ~Collinear A O B  /\  beta = angle A O B /\
             G IN int_angle A O B  /\  alpha === angle A O G`;;

let RAY = new_definition
 `Ray r  <=>  ? O A. ~(O = A) /\ r = ray O A`;;

let TriangleCong_DEF = new_definition
 `! A B C A' B' C' :point. (A, B, C) cong (A', B', C')  <=>
  ~Collinear A B C /\ ~Collinear A' B' C' /\
  seg A B === seg A' B' /\ seg A C === seg A' C' /\ seg B C === seg B' C' /\
  angle A B C === angle A' B' C' /\
  angle B C A === angle B' C' A' /\
  angle C A B === angle C' A' B'`;;

let SupplementaryAngles_DEF = new_definition
 `! alpha beta. alpha suppl beta   <=>
  ? A O B A'. ~Collinear A O B  /\  O IN open (A,A')  /\  alpha = angle A O B  /\  beta = angle B O A'`;;

let RightAngle_DEF = new_definition
 `! alpha. Right alpha  <=>  ? beta. alpha suppl beta /\ alpha === beta`;;

let PlaneComplement_DEF = new_definition
 `! alpha:point_set. complement alpha = {P | P NOTIN alpha}`;;

let CONVEX = new_definition
 `Convex alpha  <=>  ! A B. A IN alpha /\ B IN alpha  ==> open (A,B) SUBSET alpha`;;

let PARALLEL = new_definition
 `! l k. l parallel k   <=>
  Line l /\ Line k /\ l INTER k = {}`;;

let Parallelogram_DEF = new_definition
  `! A B C D. Parallelogram A B C D  <=>
  Quadrilateral A B C D /\ ? a b c d.
  Line a /\ A IN a /\ B IN a /\
  Line b /\ B IN b /\ C IN b /\
  Line c  /\ C IN c /\ D IN d /\
  Line d /\ D IN d /\ A IN d /\
  a parallel c  /\  b parallel d`;;

let InteriorCircle_DEF = new_definition
 `! O R.  int_circle O R = {P | ~(O = R) /\ (P = O  \/  seg O P <__ seg O R)}
`;;


(* ----------------------------------------------------------------------------  *)
(* Hilbert's geometry axioms, except the parallel axiom P, defined near the end. *)
(* ----------------------------------------------------------------------------  *)


let I1 = new_axiom
  `! A B.  ~(A = B) ==> ?! l. Line l /\  A IN l /\ B IN l`;;

let I2 = new_axiom
  `! l. Line l  ==>  ? A B. A IN l /\ B IN l /\ ~(A = B)`;;

let I3 = new_axiom
  `? A B C. ~(A = B) /\ ~(A = C) /\ ~(B = C) /\
                             ~Collinear A B C`;;

let B1 = new_axiom
  `! A B C. Between A B C ==> ~(A = B) /\ ~(A = C) /\ ~(B = C) /\
            Between C B A /\ Collinear A B C`;;

let B2 = new_axiom
  `! A B. ~(A = B) ==> ? C. Between A B C`;;

let B3 = new_axiom
  `! A B C. ~(A = B) /\ ~(A = C) /\ ~(B = C) /\ Collinear A B C
    ==> (Between A B C \/ Between B C A \/ Between C A B) /\
        ~(Between A B C /\ Between B C A) /\
        ~(Between A B C /\ Between C A B) /\
        ~(Between B C A /\ Between C A B)`;;

let B4 = new_axiom
  `! l A B C. Line l /\ ~Collinear A B C /\
   A NOTIN l /\ B NOTIN l /\ C NOTIN l /\
   (? X. X IN l /\ Between A X C) ==>
   (? Y. Y IN l /\ Between A Y B) \/ (? Y. Y IN l /\ Between B Y C)`;;

let C1 = new_axiom
  `! s O Z. Segment s /\ ~(O = Z)  ==>
   ?! P. P IN ray O Z DELETE O  /\  seg O P === s`;;

let C2Reflexive = new_axiom
  `Segment s  ==>  s === s`;;

let C2Symmetric = new_axiom
  `Segment s /\ Segment t /\ s === t  ==>  t === s`;;

let C2Transitive = new_axiom
  `Segment s /\ Segment t /\ Segment u /\
   s === t /\ t === u ==>  s === u`;;

let C3 = new_axiom
  `! A B C A' B' C'.  B IN open (A,C) /\ B' IN open (A',C') /\
  seg A B === seg A' B' /\ seg B C === seg B' C'  ==>
  seg A C === seg A' C'`;;

let C4 = new_axiom
 `! alpha O A l Y. Angle alpha /\ ~(O = A) /\ Line l /\ O IN l /\ A IN l /\ Y NOTIN l
    ==> ?! r. Ray r  /\  ? B. ~(O = B)  /\  r = ray O B  /\
          B NOTIN l  /\  B,Y same_side l  /\  angle A O B === alpha`;;

let C5Reflexive = new_axiom
  `Angle alpha  ==>  alpha === alpha`;;

let C5Symmetric = new_axiom
  `Angle alpha /\ Angle beta /\ alpha === beta  ==>  beta === alpha`;;

let C5Transitive = new_axiom
  `Angle alpha /\ Angle beta /\ Angle gamma /\
   alpha === beta /\ beta === gamma ==>  alpha === gamma`;;

let C6 = new_axiom
  `! A B C A' B' C'. ~Collinear A B C /\ ~Collinear A' B' C' /\
   seg B A === seg B' A' /\ seg B C === seg B' C' /\ angle A B C === angle A' B' C'
   ==> angle B C A === angle B' C' A'`;;


(* ----------------------------------------------------------------- *)
(* Theorems.                                                         *)
(* ----------------------------------------------------------------- *)


let IN_Interval = thm `;
 ! A B X. X IN open (A,B)  <=>  Between A X B
 by Interval_DEF, SET_RULE;
`;;

let IN_Ray = thm `;
 ! A B X. X IN ray A B  <=>  ~(A = B) /\ Collinear A B X /\ A NOTIN open (X,B)
 by Ray_DEF, SET_RULE;
`;;

let IN_InteriorAngle = thm `;
 ! A O B P. P IN int_angle A O B  <=>
     ~Collinear A O B /\ ? a b.
     Line a /\ O IN a /\ A IN a /\ Line b /\ O IN b /\ B IN b /\
     P NOTIN a /\ P NOTIN b /\ P,B same_side a /\ P,A same_side b
 by InteriorAngle_DEF, SET_RULE;
`;;

let IN_InteriorTriangle = thm `;
 ! A B C P. P IN int_triangle A B C  <=>
     P IN int_angle A B C  /\  P IN int_angle B C A  /\  P IN int_angle C A B
 by InteriorTriangle_DEF, SET_RULE;
`;;

let IN_PlaneComplement = thm `;
  ! alpha:point_set. ! P. P IN complement alpha  <=>  P NOTIN alpha
  by PlaneComplement_DEF, SET_RULE;
`;;

let IN_InteriorCircle = thm `;
 ! O R P. P IN int_circle O R  <=>
     ~(O = R) /\ (P = O  \/  seg O P <__ seg O R)
 by InteriorCircle_DEF, SET_RULE;
`;;

let B1' = thm `;
  ! A B C.  B IN open (A,C) ==> ~(A = B) /\ ~(A = C) /\ ~(B = C) /\
             B IN open (C,A) /\ Collinear A B C
  by IN_Interval, B1;
`;;

let B2' = thm `;
  ! A B. ~(A = B) ==> ? C.  B IN open (A,C)
  by IN_Interval, B2;
`;;

let B3' = thm `;
  ! A B C. ~(A = B) /\ ~(A = C) /\ ~(B = C) /\ Collinear A B C
    ==> (B IN open (A,C) \/ C IN open (B,A) \/ A IN open (C,B)) /\
        ~(B IN open (A,C) /\ C IN open (B,A)) /\
        ~(B IN open (A,C) /\ A IN open (C,B)) /\
        ~(C IN open (B,A) /\ A IN open (C,B))
  by IN_Interval, B3;
`;;

let B4' = thm `;
  ! l A B C. Line l /\ ~Collinear A B C /\
   A NOTIN l /\ B NOTIN l /\ C NOTIN l /\
   (? X. X IN l /\  X IN open (A,C)) ==>
   (? Y. Y IN l /\  Y IN open (A,B)) \/ (? Y. Y IN l /\  Y IN open (B,C))
   by IN_Interval, B4;
`;;

let B4'' = thm `;
  ! l:point_set. ! A B C:point.
  Line l /\ ~Collinear A B C /\ A NOTIN l /\ B NOTIN l /\ C NOTIN l  /\
  A,B same_side l  /\  B,C same_side l  ==>  A,C same_side l
  by B4', SameSide_DEF;
`;;

let DisjointOneNotOther = thm `;
  ! l m:A->bool. (! x:A. x IN m  ==> x NOTIN l)  <=>  l INTER m = {}
  by SET_RULE, NOTIN;
`;;

let EquivIntersectionHelp = thm `;
  ! e x:A. ! l m:A->bool.
  (l INTER m = {x}  \/  m INTER l = {x})  /\  e IN m DELETE x   ==>  e NOTIN l
  by SET_RULE, NOTIN;
`;;

let CollinearSymmetry = thm `;
  let A B C be point;
  assume Collinear A B C     [H1];
  thus Collinear A C B /\ Collinear B A C /\ Collinear B C A /\
       Collinear C A B /\ Collinear C B A

  proof
    consider l such that
    Line l /\ A IN l /\ B IN l /\ C IN l     by H1, Collinear_DEF;
  qed     by -, Collinear_DEF;
`;;

let ExistsNewPointOnLine = thm `;
  let P be point;
  let l be point_set;
  assume Line l /\ P IN l [H1];
  thus ? Q. Q IN l /\ ~(P = Q)

  proof
    consider A B such that
    A IN l /\ B IN l /\ ~(A = B)    [l_line] by H1, I2;
    cases;
    suppose P = A;
    qed by -, l_line;
    suppose ~(P = A);
    qed by -, l_line;
  end;
`;;

let ExistsPointOffLine = thm `;
  let l be point_set;
  assume Line l     [H1];
  thus ? Q:point. Q NOTIN l

  proof
    consider A B C such that
    ~(A = B) /\ ~(A = C) /\ ~(B = C) /\ ~Collinear A B C     [Distinct] by I3;
    (A NOTIN l \/ B NOTIN l \/ C NOTIN l) \/ (A IN l /\ B IN l /\ C IN l) by NOTIN;
    cases by -;
    suppose A NOTIN l \/ B NOTIN l \/ C NOTIN l;
    qed     by -;
    suppose (A IN l) /\ (B IN l) /\ (C IN l);
      Collinear A B C     by H1, -, Collinear_DEF;
    qed     by -, Distinct;
  end;
`;;

let BetweenLinear = thm `;
  let A B C be point;
  let m be point_set;
  assume Line m /\ A IN m /\ C IN m     [H1];
  assume B IN open (A,C) \/ C IN open (B,A)  \/ A IN open (C,B)     [H2];
  thus B IN m

  proof
    ~(A = C) /\
    (Collinear A B C \/ Collinear B C A \/ Collinear C A B)     [X1] by H2, B1';
    consider l such that
    Line l /\ A IN l /\ B IN l /\ C IN l     [X2] by -, Collinear_DEF;
    l = m     by X1, -, H2, H1, I1;
  qed     by -, X2;
`;;

let CollinearLinear = thm `;
  let A B C be point;
  let m be point_set;
  assume Line m /\ A IN m /\ C IN m     [H1];
  assume Collinear A B C \/ Collinear B C A \/ Collinear C A B     [H2];
  assume ~(A = C)     [H3];
  thus B IN m

  proof
    consider l such that
    Line l /\ A IN l /\ B IN l /\ C IN l     [X1] by H2, Collinear_DEF;
    l = m     by H3, -, H1, I1;
  qed     by -, X1;
`;;

let NonCollinearImpliesDistinct = thm `;
  let A B C be point;
  assume ~Collinear A B C     [H1];
  thus ~(A = B) /\ ~(A = C) /\ ~(B = C)

  proof
    cases;
    suppose A = B /\ B = C     [Case1];
      consider Q such that
      ~(Q = A)     by I3;
    qed     by -, I1, Case1, Collinear_DEF, H1;
    suppose (A = B /\ ~(A = C)) \/  (A = C /\ ~(A = B)) \/ (B = C /\ ~(A = B));
    qed by -, I1, Collinear_DEF, H1;
    suppose ~(A = B) /\ ~(A = C) /\ ~(B = C);
    qed by -;
  end;
`;;

let Reverse4Order = thm `;
  ! A B C D:point. ordered A B C D  ==>  ordered D C B A
  by Ordered_DEF, B1';
`;;

let OriginInRay = thm `;
  let O Q be point;
  assume ~(Q = O)     [H1];
  thus O IN ray O Q

  proof
    O NOTIN open (O,Q)     [OOQ] by B1', NOTIN;
    Collinear O Q O     by H1, I1, Collinear_DEF;
  qed     by H1, -, OOQ, IN_Ray;
`;;

let EndpointInRay = thm `;
  let O Q be point;
  assume ~(Q = O)     [H1];
  thus Q IN ray O Q

  proof
    O NOTIN open (Q,Q)     [notOQQ] by B1', NOTIN;
    Collinear O Q Q     by H1, I1, Collinear_DEF;
  qed     by H1, -, notOQQ, IN_Ray;
`;;

let I1Uniqueness = thm `;
  let X be point;
  let l m be point_set;
  assume Line l /\ Line m        [H0];
  assume ~(l = m)               [H1];
  assume X IN l /\ X IN m          [H2];
  thus l INTER m = {X}

  proof
    assume ~(l INTER m = {X})     [H3];
    X IN l INTER m     by H2, IN_INTER;
    consider A such that
    A IN l INTER m  /\ ~(A = X)     [X1] by -, H3, SET_RULE;
    A IN l /\ X IN l /\ A IN m /\ X IN m     by H0, -, H2, IN_INTER;
    l = m     by H0, -, X1, I1;
  qed     by -, H1;
`;;

let EquivIntersection = thm `;
  let A B X be point;
  let l m be point_set;
  assume Line l /\ Line m                [H0];
  assume l INTER m = {X}                    [H1];
  assume A IN m DELETE X /\ B IN m DELETE X          [H2];
  assume X NOTIN open (A,B)                 [H3];
  thus  A,B same_side l

  proof
    assume ~(A,B same_side l) [Con];
    A IN m /\ B IN m /\ ~(A = X) /\ ~(B = X)     [H2'] by H2, IN_DELETE;
    ~(open (A,B) INTER l = {})     [nonempty] by H0, Con, SameSide_DEF, SET_RULE;
    open (A,B) SUBSET m     [ABm] by H0, H2', BetweenLinear, SUBSET;
    open (A,B) INTER l  SUBSET  {X}     by -, SET_RULE, H1;
    X IN open (A,B) INTER l     by nonempty, -, SET_RULE;
  qed     by -, IN_INTER, H3, NOTIN;
`;;

let RayLine = thm `;
  ! O P:point. ! l: point_set.
  Line l /\ O IN l /\ P IN l  ==>  ray O P  SUBSET l
  by IN_Ray, CollinearLinear, SUBSET;
`;;

let RaySameSide = thm `;
  let l be point_set;
  let O A P be point;
  assume Line l /\ O IN l         [l_line];
  assume A NOTIN l                  [notAl];
  assume P IN ray O A DELETE O                [PrOA];
  thus P NOTIN l  /\  P,A same_side l

  proof
    ~(O = A)     [notOA] by l_line, notAl, NOTIN;
    consider d such that
    Line d /\ O IN d /\ A IN d     [d_line] by notOA, I1;
    ~(l = d)     by -, notAl, NOTIN;
    l INTER d = {O}     [ldO] by l_line, d_line, -, I1Uniqueness;
    A IN d DELETE O     [Ad_O] by d_line, notOA, IN_DELETE;
    ray O A SUBSET d     by d_line, RayLine;
    P IN d DELETE O     [Pd_O] by PrOA, -, SUBSET, IN_DELETE;
    P NOTIN l     [notPl] by ldO, -, EquivIntersectionHelp;
    O NOTIN open (P,A)     by PrOA, IN_DELETE, IN_Ray;
    P,A same_side l     by l_line, d_line, ldO, Ad_O, Pd_O, -, EquivIntersection;
  qed     by notPl, -;
`;;

let IntervalRayEZ = thm `;
  let A B C be point;
  assume B IN open (A,C)                         [H1];
  thus B IN ray A C DELETE A  /\  C IN ray A B DELETE A

  proof
    ~(A = B) /\ ~(A = C) /\ ~(B = C) /\ Collinear A B C     [ABC] by H1, B1';
    A NOTIN open (B,C)  /\  A NOTIN open (C,B)     by -, H1, B3', B1', NOTIN;
  qed     by ABC, CollinearSymmetry, -, IN_Ray, IN_DELETE, NOTIN;
`;;

let NoncollinearityExtendsToLine = thm `;
  let A O B X be point;
  assume ~Collinear A O B                       [H1];
  assume Collinear O B X  /\ ~(X = O)            [H2];
  thus ~Collinear A O X

  proof
    ~(A = O) /\ ~(A = B) /\ ~(O = B)     [Distinct] by H1, NonCollinearImpliesDistinct;
    consider b such that
    Line b /\ O IN b /\ B IN b     [b_line] by Distinct, I1;
    A NOTIN b     [notAb] by b_line, Collinear_DEF, H1, NOTIN;
    X IN b     by H2, b_line, Distinct, I1, Collinear_DEF;
  qed     by b_line, -, H2, I1, Collinear_DEF, notAb, NOTIN;
`;;

let SameSideReflexive = thm `;
  ! l A. Line l /\  A NOTIN l ==> A,A same_side l
  by B1', SameSide_DEF;
`;;

let SameSideSymmetric = thm `;
  ! l A B. Line l /\  A NOTIN l /\ B NOTIN l ==>
  A,B same_side l ==> B,A same_side l
  by SameSide_DEF, B1';
`;;

let SameSideTransitive = thm `;
  let l be point_set;
  let A B C be point;
  assume Line l                         [l_line];
  assume A NOTIN l /\ B NOTIN l /\ C NOTIN l          [notABCl];
  assume A,B same_side l                [Asim_lB];
  assume B,C same_side l                [Bsim_lC];
  thus A,C same_side l

  proof
    cases;
    suppose ~Collinear A B C  \/  A = B \/ A = C \/ B = C;
    qed     by l_line, -, notABCl, Asim_lB, Bsim_lC, B4'', SameSideReflexive;
    suppose Collinear A B C  /\ ~(A = B) /\ ~(A = C) /\ ~(B = C)     [Distinct];
      consider m such that
      Line m /\ A IN m /\ C IN m     [m_line] by Distinct, I1;
      B IN m     [Bm] by -, Distinct, CollinearLinear;
      cases;
      suppose m INTER l = {};
      qed     by m_line, l_line, -, BetweenLinear, SET_RULE, SameSide_DEF;
      suppose ~(m INTER l = {});
        consider X such that
        X IN l /\ X IN m     [Xlm] by -, MEMBER_NOT_EMPTY, IN_INTER;
        Collinear A X B  /\  Collinear B A C  /\  Collinear A B C     [ABXcol] by m_line, Bm, -, Collinear_DEF;
        consider E such that
        E IN l /\ ~(E = X)     [El_X] by l_line, Xlm, ExistsNewPointOnLine;
        ~Collinear E A X     [EAXncol] by  l_line, El_X, Xlm, I1, Collinear_DEF, notABCl, NOTIN;
        consider B' such that
        ~(B = E)  /\  B IN open (E,B')     [EBB'] by notABCl, El_X, NOTIN, B2';
        ~(B' = E) /\ ~(B' = B) /\ Collinear B E B'     [EBB'col] by -, B1', CollinearSymmetry;
        ~Collinear A B B'  /\  ~Collinear B' B A  /\  ~Collinear B' A B     [ABB'ncol] by EAXncol, ABXcol, Distinct, NoncollinearityExtendsToLine, CollinearSymmetry, -;
        ~Collinear B' B C /\  ~Collinear B' A C /\  ~Collinear A B' C     [AB'Cncol] by ABB'ncol, ABXcol, Distinct, NoncollinearityExtendsToLine, CollinearSymmetry;
        B' IN ray E B DELETE E  /\  B IN ray E B' DELETE E     by EBB', IntervalRayEZ;
        B' NOTIN l  /\  B',B same_side l  /\  B,B' same_side l     [notB'l] by l_line, El_X, notABCl, -, RaySameSide;
        A,B' same_side l /\  B',C same_side l     by l_line, ABB'ncol, notABCl, notB'l, Asim_lB, -, B4'', AB'Cncol, Bsim_lC;
      qed     by l_line, AB'Cncol, notABCl, notB'l, -, B4'';
    end;
  end;
`;;

let ConverseCrossbar = thm `;
  let O A B G be point;
  assume ~Collinear A O B     [H1];
  assume G IN open (A,B)     [H2];
  thus G IN int_angle A O B

  proof
    ~(A = O) /\ ~(A = B) /\ ~(O = B)     [Distinct] by H1, NonCollinearImpliesDistinct;
    consider a such that
    Line a /\ O IN a /\ A IN a     [a_line] by -, I1;
    consider b such that
    Line b /\ O IN b /\ B IN b     [b_line] by Distinct, I1;
    consider l such that
    Line l /\ A IN l /\ B IN l     [l_line] by Distinct, I1;
     B NOTIN a  /\  A NOTIN b     by H1, a_line, Collinear_DEF, NOTIN, b_line;
    ~(a = l)  /\  ~(b = l)     by -, l_line, NOTIN;
    a INTER l = {A}  /\  b INTER l = {B}     [alA] by -, a_line, l_line, I1Uniqueness, b_line;
    ~(A = G) /\ ~(A = B) /\ ~(G = B)     [AGB] by H2, B1';
    A NOTIN open (G,B)  /\  B NOTIN open (G,A)     [notGAB] by H2, B3', B1', NOTIN;
    G IN l     [Gl] by l_line, H2, BetweenLinear;
    G NOTIN a  /\  G NOTIN b     [notGa] by alA, Gl, AGB, IN_DELETE, EquivIntersectionHelp;
    G IN l DELETE A /\ B IN l DELETE A /\ G IN l DELETE B /\ A IN l DELETE B      by Gl, l_line, AGB, IN_DELETE;
    G,B same_side a  /\  G,A same_side b     by a_line, l_line, alA, -, notGAB, EquivIntersection, b_line;
  qed     by H1, a_line, b_line, notGa, -, IN_InteriorAngle;
`;;

let InteriorUse = thm `;
  let A O B P be point;
  let a b be point_set;
  assume Line a /\ O IN a /\ A IN a /\ Line b /\ O IN b /\ B IN b     [aOAbOB];
  assume  P  IN int_angle A O B     [P_AOB];
  thus P NOTIN a /\ P NOTIN b /\ P,B same_side a /\ P,A same_side b

  proof
    consider alpha beta such that ~Collinear A O B /\
    Line alpha /\ O IN alpha /\ A IN alpha /\
    Line beta /\ O IN beta /\B IN beta /\
    P NOTIN alpha /\ P NOTIN beta /\
    P,B same_side alpha /\ P,A same_side beta     [exists] by P_AOB, IN_InteriorAngle;
    ~(A = O) /\ ~(A = B) /\ ~(O = B)     [Distinct] by -, NonCollinearImpliesDistinct;
    alpha = a /\ beta = b     by -, aOAbOB, exists, I1;
  qed     by -, exists;
`;;

let InteriorEZHelp = thm `;
  let A O B P be point;
  assume  P IN int_angle A O B     [P_AOB];
  thus ~(P = A) /\ ~(P = O) /\ ~(P = B) /\ ~Collinear A O P

  proof
    consider a b such that
    ~Collinear A O B /\
    Line a /\ O IN a /\ A IN a /\
    Line b /\ O IN b /\B IN b /\
    P NOTIN a /\ P NOTIN b     [def_int] by P_AOB, IN_InteriorAngle;
    ~(P = A) /\ ~(P = O) /\ ~(P = B)     [PnotAOB] by -, NOTIN;
    ~(A = O)     [notAO] by def_int, NonCollinearImpliesDistinct;
    ~Collinear A O P by def_int, notAO, -, I1, Collinear_DEF, NOTIN;
  qed     by PnotAOB, -;
`;;

let InteriorAngleSymmetry = thm `;
  ! A O B P: point. P IN int_angle A O B  ==>  P IN int_angle B O A
  by IN_InteriorAngle, CollinearSymmetry;
`;;

let InteriorWellDefined = thm `;
  let A O B X P be point;
  assume P IN int_angle A O B            [H1];
  assume X IN ray O B DELETE O                [H2];
  thus P IN int_angle A O X

  proof
    consider a b such that
    ~Collinear A O B /\
    Line a /\ O IN a /\ A IN a /\ P NOTIN a     /\     Line b /\ O IN b /\ B IN b /\ P NOTIN b /\
    P,B same_side a /\ P,A same_side b     [def_int] by H1, IN_InteriorAngle;
    ~(X = O) /\ ~(O = B) /\ Collinear O B X     [H2'] by H2, IN_DELETE, IN_Ray;
    B NOTIN a     [notBa] by def_int, Collinear_DEF, NOTIN;
    ~Collinear A O X     [AOXnoncol] by def_int, H2', NoncollinearityExtendsToLine;
    X IN b     [Xb] by def_int, H2', CollinearLinear;
    X NOTIN a  /\  B,X same_side a     by def_int, notBa, H2, RaySameSide, SameSideSymmetric;
    P,X same_side a     by def_int, -, notBa, SameSideTransitive;
  qed     by AOXnoncol, def_int, Xb, -, IN_InteriorAngle;
`;;

let WholeRayInterior = thm `;
  let A O B X P be point;
  assume X IN int_angle A O B            [XintAOB];
  assume P IN ray O X DELETE O                [PrOX];
  thus P IN int_angle A O B

  proof
    consider a b such that
    ~Collinear A O B /\
    Line a /\ O IN a /\ A IN a /\ X NOTIN a   /\   Line b /\ O IN b /\ B IN b /\ X NOTIN b /\
    X,B same_side a /\ X,A same_side b     [def_int] by XintAOB, IN_InteriorAngle;
    P NOTIN a /\ P,X same_side a /\ P NOTIN b /\ P,X same_side b     [Psim_abX] by def_int, PrOX, RaySameSide;
    P,B same_side a  /\ P,A same_side b     by -, def_int, Collinear_DEF, SameSideTransitive, NOTIN;
  qed     by def_int, Psim_abX, -, IN_InteriorAngle;
`;;

let AngleOrdering = thm `;
  let O A P Q be point;
  let a be point_set;
  assume ~(O = A)     [H1];
  assume Line a /\ O IN a /\ A IN a                 [H2];
  assume P NOTIN a /\ Q NOTIN a                                  [H3];
  assume P, Q same_side a                               [H4];
  assume ~Collinear P O Q                               [H5];
  thus P IN int_angle Q O A  \/  Q IN int_angle P O A

  proof
    ~(P = O) /\ ~(P = Q) /\ ~(O = Q)     [Distinct] by H5, NonCollinearImpliesDistinct;
    consider q such that
    Line q /\ O IN q /\ Q IN q     [q_line] by Distinct, I1;
    P NOTIN q     [notPq] by -, Collinear_DEF, H5, NOTIN;
    assume ~(P IN int_angle Q O A)     [notPintQOA];
    ~Collinear Q O A  /\  ~Collinear P O A     [POAncol] by H1, H2, I1, Collinear_DEF, H3, NOTIN;
    ~(P,A same_side q)     by -, H2, q_line, H3, notPq, H4, notPintQOA, IN_InteriorAngle;
    consider G such that
    G IN q /\ G IN open (P,A)     [existG] by q_line, -, SameSide_DEF;
    G IN int_angle P O A     [G_POA] by  POAncol, existG, ConverseCrossbar;
    G NOTIN a /\ G,P same_side a /\ ~(G = O)    [Gsim_aP] by -, IN_InteriorAngle, H1, H2, I1, NOTIN;
    G,Q same_side a     by H2, Gsim_aP, H3, H4, SameSideTransitive;
    O NOTIN open (Q,G)     [notQOG] by -, SameSide_DEF, H2, B1', NOTIN;
    Collinear O G Q     by q_line, existG, Collinear_DEF;
    Q IN ray O G DELETE O     by Gsim_aP, -, notQOG, IN_Ray, Distinct, IN_DELETE;
  qed     by G_POA, -, WholeRayInterior;
`;;

let InteriorsDisjointSupplement = thm `;
  let A O B A' be point;
  assume ~Collinear A O B                               [H1];
  assume O IN open (A,A')                                [H2];
  thus  int_angle B O A'  INTER  int_angle A O B = {}

  proof
    ! D. D IN int_angle A O B  ==>  D NOTIN int_angle B O A'
    proof
      let D be point;
      assume D IN int_angle A O B     [H3];
      ~(A = O) /\ ~(O = B)     by H1, NonCollinearImpliesDistinct;
      consider a b such that
      Line a /\ O IN a /\ A IN a /\ Line b /\ O IN b /\ B IN b /\ A' IN a     [ab_line] by -, I1, H2, BetweenLinear;
      ~Collinear B O A'     by H1, CollinearSymmetry, H2, B1', NoncollinearityExtendsToLine;
      A NOTIN b  /\  A' NOTIN b     [notAb] by ab_line, Collinear_DEF, H1, -, NOTIN;
      ~(A',A same_side b)     [A'nsim_bA] by ab_line, H2, B1', SameSide_DEF ;
      D NOTIN b  /\  D,A same_side b     [DintAOB] by ab_line, H3, InteriorUse;
      ~(D,A' same_side b)     by ab_line, notAb, DintAOB, A'nsim_bA, SameSideSymmetric, SameSideTransitive;
      qed     by ab_line, -, InteriorUse, NOTIN;
  qed by -, DisjointOneNotOther;
`;;

let InteriorReflectionInterior = thm `;
  let A O B D A' be point;
  assume O IN open (A,A')                [H1];
  assume D IN int_angle A O B            [H2];
  thus B  IN int_angle D O A'

  proof
    consider a b such that
    ~Collinear A O B /\ Line a /\ O IN a /\ A IN a /\ D NOTIN a /\
    Line b /\ O IN b /\ B IN b /\ D NOTIN b /\ D,B same_side a     [DintAOB] by H2, IN_InteriorAngle;
    ~(O = B) /\ ~(O = A') /\ B NOTIN a     [Distinct] by -, NonCollinearImpliesDistinct, H1, B1', Collinear_DEF, NOTIN;
    ~Collinear D O B     [DOB_ncol] by DintAOB, -, I1, Collinear_DEF, NOTIN;
    A' IN a     [A'a] by H1, DintAOB, BetweenLinear;
    D NOTIN int_angle B O A'     by DintAOB, H1, InteriorsDisjointSupplement, H2, DisjointOneNotOther;
  qed     by Distinct, DintAOB, A'a, DOB_ncol, -, AngleOrdering, NOTIN;
`;;

let Crossbar_THM = thm `;
  let O A B D be point;
  assume D IN int_angle A O B     [H1];
  thus ? G. G IN open (A,B)  /\  G IN ray O D DELETE O

  proof
    consider a b such that
    ~Collinear A O B /\
    Line a /\ O IN a /\ A IN a /\
    Line b /\ O IN b /\ B IN b /\
    D NOTIN a /\ D NOTIN b /\ D,B same_side a /\ D,A same_side b     [DintAOB] by H1, IN_InteriorAngle;
    B NOTIN a     [notBa] by DintAOB, Collinear_DEF, NOTIN;
    ~(A = O) /\ ~(A = B) /\ ~(O = B) /\ ~(D = O)     [Distinct] by DintAOB, NonCollinearImpliesDistinct, NOTIN;
    consider l such that
    Line l /\ O IN l /\ D IN l     [l_line] by -, I1;
    consider A' such that
    O IN open (A,A')     [AOA'] by Distinct, B2';
    A' IN a /\ Collinear A O A' /\ ~(A' = O)      [A'a] by DintAOB, -, BetweenLinear, B1';
    ~(A,A' same_side l)     [Ansim_lA'] by l_line, AOA', SameSide_DEF;
    B IN int_angle D O A'     by H1, AOA', InteriorReflectionInterior;
    B,A' same_side l     [Bsim_lA'] by l_line, DintAOB, A'a, -, InteriorUse;
    ~Collinear A O D  /\  ~Collinear B O D      [AODncol] by H1, InteriorEZHelp, InteriorAngleSymmetry;
    ~Collinear D O A'      by -, CollinearSymmetry, A'a, NoncollinearityExtendsToLine;
    A NOTIN l /\ B NOTIN l /\ A' NOTIN l     by l_line, Collinear_DEF, AODncol, -, NOTIN;
    ~(A,B same_side l)     by l_line, -, Bsim_lA', Ansim_lA', SameSideTransitive;
    consider G such that
    G IN open (A,B) /\ G IN l     [AGB] by l_line, -, SameSide_DEF;
    Collinear O D G     [ODGcol] by -, l_line, Collinear_DEF;
    G IN int_angle A O B     by DintAOB, AGB, ConverseCrossbar;
    G NOTIN a  /\  G,B same_side a  /\  ~(G = O)     [Gsim_aB] by DintAOB, -, InteriorUse, NOTIN;
    B,D same_side a     by DintAOB, notBa, SameSideSymmetric;
    G,D same_side a     [Gsim_aD] by DintAOB, Gsim_aB, notBa, -, SameSideTransitive;
    O NOTIN open (G,D)     by DintAOB, -, SameSide_DEF, NOTIN;
    G IN ray O D DELETE O     by Distinct, ODGcol, -, IN_Ray, Gsim_aB, IN_DELETE;
  qed     by AGB, -;
`;;

let AlternateConverseCrossbar = thm `;
  let O A B G be point;
  assume Collinear A G B  /\  G IN int_angle A O B                [H1];
  thus G IN open (A,B)

  proof
    consider a b such that
    ~Collinear A O B  /\  Line a /\ O IN a /\ A IN a  /\  Line b /\ O IN b /\ B IN b  /\
    G,B same_side a  /\  G,A same_side b     [GintAOB] by H1, IN_InteriorAngle;
    ~(A = B) /\ ~(G = A) /\ ~(G = B)  /\  A NOTIN open (G,B)  /\  B NOTIN open (G,A)     by -, NonCollinearImpliesDistinct, H1, InteriorEZHelp, SameSide_DEF, NOTIN;
  qed     by -, H1, B1', B3', NOTIN;
`;;

let InteriorOpposite = thm `;
  let A O B P be point;
  let p be point_set;
  assume P IN int_angle A O B            [PintAOB];
  assume Line p /\ O IN p /\ P IN p         [p_line];
  thus ~(A,B same_side p)

  proof
    consider G such that
    G IN open (A,B) /\ G IN ray O P     [Gexists] by PintAOB, Crossbar_THM, IN_DELETE;
    G IN p     by p_line, RayLine, -, SUBSET;
  qed     by p_line, -, Gexists, SameSide_DEF;
`;;

let IntervalTransitivity = thm `;
  let O P Q R be point;
  let m be point_set;
  assume Line m  /\ O IN m                                [H0];
  assume P IN m DELETE O /\ Q IN m DELETE O /\ R IN m DELETE O      [H2];
  assume O NOTIN open (P,Q) /\ O NOTIN open (Q,R)                [H3];
  thus O NOTIN open (P,R)

  proof
    consider E such that
    E NOTIN m /\  ~(O = E)     [notEm] by H0, ExistsPointOffLine, NOTIN;
    consider l such that
    Line l /\ O IN l /\ E IN l     [l_line] by -, I1;
    ~(m = l)     by notEm, -, NOTIN;
    l INTER m = {O}     [lmO] by l_line, H0, -, l_line, I1Uniqueness;
    P NOTIN l /\  Q NOTIN l /\ R NOTIN l     [notPQRl] by -, H2, EquivIntersectionHelp;
    P,Q same_side l  /\  Q,R same_side l     by l_line, H0, lmO, H2, H3, EquivIntersection;
    P,R same_side l     [Psim_lR] by l_line, notPQRl, -, SameSideTransitive;
  qed     by l_line, -, SameSide_DEF, NOTIN;
`;;

let RayWellDefinedHalfway = thm `;
  let O P Q be point;
  assume ~(Q = O)               [H1];
  assume P IN ray O Q DELETE O        [H2];
  thus ray O P SUBSET ray O Q

  proof
    consider m such that
    Line m /\ O IN m /\ Q IN m     [OQm] by H1, I1;
    P IN ray O Q  /\  ~(P = O)  /\  O NOTIN open (P,Q)     [H2'] by H2, IN_DELETE, IN_Ray;
    P IN m  /\  P IN m DELETE O  /\  Q IN m DELETE O     [PQm_O] by OQm, H2', RayLine, SUBSET, H2', OQm, H1, IN_DELETE;
    O NOTIN open (P,Q)     [notPOQ] by H2', IN_Ray;
    ! X. X IN ray O P ==> X IN ray O Q
    proof
      let X be point;
      assume X IN ray O P;
      X IN m  /\  O NOTIN open (X,P)     [XrOP] by OQm, PQm_O, H2', -, RayLine, SUBSET, IN_Ray;
      Collinear O Q X     [OQXcol] by OQm, -,  Collinear_DEF;
      cases;
      suppose X = O;
      qed     by H1, -, OriginInRay;
      suppose ~(X = O);
        X IN m DELETE O     by XrOP, -, IN_DELETE;
        O NOTIN open (X,Q)     by OQm, -, PQm_O, XrOP, H2', IntervalTransitivity;
      qed     by H1, OQXcol, -, IN_Ray;
    end;
  qed     by -, SUBSET;
`;;

let RayWellDefined = thm `;
  let O P Q be point;
  assume ~(Q = O)                       [H1];
  assume P IN ray O Q DELETE O                [H2];
  thus ray O P = ray O Q

  proof
    ray O P SUBSET ray O Q     [PsubsetQ] by H1, H2, RayWellDefinedHalfway;
    ~(P = O)  /\  Collinear O Q P  /\  O NOTIN open (P,Q)     [H2'] by H2, IN_DELETE, IN_Ray;
    Q IN ray O P DELETE O     by H2', B1', NOTIN, CollinearSymmetry, IN_Ray, H1, IN_DELETE;
    ray O Q SUBSET ray O P     [QsubsetP] by H2', -, RayWellDefinedHalfway;
  qed     by PsubsetQ, QsubsetP, SUBSET_ANTISYM;
`;;

let OppositeRaysIntersect1pointHelp = thm `;
  let A O B X be point;
  assume O IN open (A,B)                 [H1];
  assume X IN ray O B DELETE O                        [H2];
  thus X NOTIN ray O A  /\  O IN open (X,A)

  proof
    ~(A = O) /\ ~(A = B) /\ ~(O = B) /\ Collinear A O B     [AOB] by H1, B1';
    ~(X = O) /\ Collinear O B X /\ O NOTIN open (X,B)     [H2'] by H2, IN_DELETE, IN_Ray;
    consider m such that
    Line m /\ A IN m /\ B IN m     [m_line] by AOB, I1;
    O IN m  /\ X IN m     [Om] by m_line, H2', AOB, CollinearLinear;
    A IN m DELETE O  /\  X IN m DELETE O  /\  B IN m DELETE O     by m_line, -, H2', AOB, IN_DELETE;
    O IN open (X,A)     by H1, m_line, Om, -, H2', IntervalTransitivity, NOTIN, B1';
  qed     by -, IN_Ray, NOTIN;
`;;

let OppositeRaysIntersect1point = thm `;
  let A O B be point;
  assume O IN open (A,B)                 [H1];
  thus ray O A INTER ray O B  =  {O}

  proof
    ~(A = O) /\ ~(O = B)     by H1, B1';
    {O}  SUBSET  ray O A INTER ray O B     [Osubset_rOA] by -, OriginInRay, IN_INTER, SING_SUBSET;
    ! X. ~(X = O)  /\  X IN ray O B  ==>  X NOTIN ray O A
    by IN_DELETE, H1, OppositeRaysIntersect1pointHelp;
    ray O A INTER ray O B  SUBSET  {O}     by -, IN_INTER, IN_SING, SUBSET, NOTIN;
  qed     by -, Osubset_rOA, SUBSET_ANTISYM;
`;;

let IntervalRay = thm `;
  ! A B C:point. B IN open (A,C)  ==>  ray A B = ray A C
  by B1', IntervalRayEZ, RayWellDefined;
`;;

let TransitivityBetweennessHelp = thm `;
  let A B C D be point;
  assume B IN open (A,C)  /\  C IN open (B,D)     [H1];
  thus B IN open (A,D)

  proof
    D IN ray B C DELETE B     by H1, IntervalRayEZ;
  qed     by H1, -, OppositeRaysIntersect1pointHelp, B1';
`;;

let TransitivityBetweenness = thm `;
  let A B C D be point;
  assume B IN open (A,C)  /\  C IN open (B,D)     [H1];
  thus ordered A B C D

  proof
    B IN open (A,D)     [ABD] by H1, TransitivityBetweennessHelp;
    C IN open (D,B)  /\  B IN open (C,A)     by H1, B1';
    C IN open (D,A)     by -, TransitivityBetweennessHelp;
  qed     by H1, ABD, -, B1', Ordered_DEF;
`;;

let IntervalsAreConvex = thm `;
 let A B C be point;
  assume B IN open (A,C)         [H1];
  thus open (A,B)  SUBSET  open (A,C)

  proof
    ! X. X IN open (A,B)  ==>  X IN open (A,C)
    proof
      let X be point;
      assume X IN open (A,B)     [AXB];
      X IN ray B A DELETE B     by AXB, B1', IntervalRayEZ;
      B IN open (X,C)     by H1, B1', -, OppositeRaysIntersect1pointHelp;
    qed     by AXB, -, TransitivityBetweennessHelp;
  qed     by -, SUBSET;
`;;

let TransitivityBetweennessVariant = thm `;
  let A X B C be point;
  assume X IN open (A,B)  /\  B IN open (A,C)     [H1];
  thus ordered A X B C

  proof
    X IN ray B A DELETE B     by H1, B1', IntervalRayEZ;
    B IN open (X,C)     by H1, B1', -, OppositeRaysIntersect1pointHelp;
  qed     by H1, -, TransitivityBetweenness;
`;;

let Interval2sides2aLineHelp = thm `;
  let A B C X be point;
  assume B IN open (A,C)                 [H1];
  thus X NOTIN open (A,B) \/ X NOTIN open (B,C)

  proof
    assume ~(X NOTIN open (A,B));
    ordered A X B C     by -, NOTIN, H1, TransitivityBetweennessVariant;
    B IN open (X,C)     by -, Ordered_DEF;
    X NOTIN open (C,B)     by -, B1', B3', NOTIN;
  qed     by -, B1', NOTIN;
`;;

let Interval2sides2aLine = thm `;
  let A B C X be point;
  assume Collinear A B C     [H1];
  thus X NOTIN open (A,B)  \/  X NOTIN open (A,C)  \/  X NOTIN open (B,C)

  proof
    cases;
    suppose A = B  \/  A = C  \/  B = C;
    qed by -, B1', NOTIN;
    suppose ~(A = B) /\ ~(A = C) /\ ~(B = C);
      B IN open (A,C)  \/  C IN open (B,A)  \/  A IN open (C,B)     by -, H1, B3';
    qed     by -, Interval2sides2aLineHelp, B1', NOTIN;
  end;
`;;

let TwosidesTriangle2aLine = thm `;
  let A B C Y be point;
  let l m be point_set;
  assume Line l /\ ~Collinear A B C                              [H1];
  assume A NOTIN l /\ B NOTIN l /\ C NOTIN l                                 [off_l];
  assume Line m /\ A IN m /\ C IN m                                 [m_line];
  assume Y IN l /\ Y IN m                                          [Ylm];
  assume ~(A,B same_side l) /\ ~(B,C same_side l)                [H2];
  thus A,C same_side l

  proof
    consider X Z such that
    X IN l  /\  X IN open (A,B)  /\  Z IN l  /\  Z IN open (C,B)     [H2'] by H1, H2, SameSide_DEF, B1';
    ~(A = B) /\ ~(A = C) /\ ~(B = C) /\ Y IN m DELETE A  /\  Y IN m DELETE C  /\  C IN m DELETE A  /\  A IN m DELETE C     [Distinct] by H1, NonCollinearImpliesDistinct, Ylm, off_l, NOTIN, m_line, IN_DELETE;
    consider p such that
    Line p /\ B IN p /\ A IN p     [p_line] by Distinct, I1;
    consider q such that
    Line q /\ B IN q /\ C IN q     [q_line] by Distinct, I1;
    X IN p  /\ Z IN q     [Xp] by p_line, H2', BetweenLinear, q_line, H2';
    A NOTIN q /\ B NOTIN m /\ C NOTIN p     [vertex_off_line] by q_line, m_line, p_line, H1, Collinear_DEF, NOTIN;
    X NOTIN q  /\  X,A same_side q  /\  Z NOTIN p  /\  Z,C same_side p     [Xsim_qA] by q_line, p_line, -, H2', B1', IntervalRayEZ, RaySameSide;
    ~(m = p)  /\  ~(m = q)     by m_line, vertex_off_line, NOTIN;
    p INTER m = {A}  /\  q INTER m = {C}     [pmA] by p_line, m_line, q_line, H1, -, Xp, H2', I1Uniqueness;
    Y NOTIN p  /\  Y NOTIN q     [notYpq] by -, Distinct, EquivIntersectionHelp;
    X IN ray A B DELETE A  /\  Z IN ray C B DELETE C     by H2', IntervalRayEZ, H2', B1';
    X NOTIN m  /\  Z NOTIN m  /\  X,B same_side m  /\  B,Z same_side m     [notXZm] by m_line, vertex_off_line, -, RaySameSide, SameSideSymmetric;
    X,Z same_side m     by m_line, -, vertex_off_line, SameSideTransitive;
    Collinear X Y Z /\ Y NOTIN open (X,Z) /\  ~(Y = X) /\ ~(Y = Z) /\ ~(X = Z)     by H1, H2', Ylm, Collinear_DEF, m_line, -, SameSide_DEF, notXZm, Xsim_qA, Xp, NOTIN;
    Z IN open (X,Y)  \/  X IN open (Z,Y)     by -, B3', NOTIN, B1';
    cases     by -;
    suppose X IN open (Z,Y);
      ~(Z,Y same_side p)     by p_line, Xp, -, SameSide_DEF;
      ~(C,Y same_side p)     by p_line, Xsim_qA, vertex_off_line, notYpq, -, SameSideTransitive;
      A IN open (C,Y)     by p_line, m_line, pmA, Distinct, -, EquivIntersection, NOTIN;
    qed     by H1, Ylm, off_l, -, B1', IntervalRayEZ, RaySameSide;
    suppose Z IN open (X,Y);
      ~(X,Y same_side q)     by q_line, Xp, -, SameSide_DEF;
      ~(A,Y same_side q)     by q_line, Xsim_qA, vertex_off_line, notYpq, -, SameSideTransitive;
      C IN open (Y,A)     by q_line, m_line, pmA, Distinct, -, EquivIntersection, NOTIN, B1';
    qed     by H1, Ylm, off_l, -, IntervalRayEZ, RaySameSide;
  end;
`;;

let LineUnionOf2Rays = thm `;
  let A O B be point;
  let l be point_set;
  assume Line l /\ A IN l /\ B IN l         [H1];
  assume O IN open (A,B)                 [H2];
  thus l = ray O A UNION ray O B

  proof
    ~(A = O) /\ ~(O = B) /\ O IN l     [Distinct] by H2, B1', H1, BetweenLinear;
    ray O A UNION ray O B  SUBSET  l     [AOBsub_l] by H1, -, RayLine, UNION_SUBSET;
    ! X. X IN l  ==>  X IN ray O A  \/  X IN ray O B
    proof
      let X be point;
      assume X IN l     [Xl];
      assume ~(X IN ray O B)     [notXrOB];
      Collinear O B X  /\  Collinear X A B  /\  Collinear O A X     [XABcol] by Distinct, H1, Xl, Collinear_DEF;
      O IN open (X,B)     by notXrOB, Distinct, -, IN_Ray, NOTIN;
      O NOTIN open (X,A)     by NOTIN, B1', XABcol, -, H2, Interval2sides2aLine;
    qed     by Distinct, XABcol, -, IN_Ray;
    l SUBSET ray O A UNION ray O B     by -, IN_UNION, SUBSET;
  qed     by -, AOBsub_l, SUBSET_ANTISYM;
`;;

let AtMost2Sides = thm `;
  let A B C be point;
  let l be point_set;
  assume Line l                                                         [H1];
  assume A NOTIN l /\ B NOTIN l /\ C NOTIN l                                          [H2];
  thus A,B same_side l  \/  A,C same_side l  \/  B,C same_side l

  proof
    cases;
    suppose A = C;
    qed     by -, H1, H2, SameSideReflexive;
    suppose ~(A = C)     [notAC];
      consider m such that
      Line m /\ A IN m /\ C IN m     [m_line] by notAC, I1;
      cases;
      suppose m INTER l = {};
        A,C same_side l     by m_line, H1, -, BetweenLinear, SET_RULE, SameSide_DEF;
      qed     by -;
      suppose ~(m INTER l = {});
        consider Y such that
        Y IN l /\ Y IN m     [Ylm] by -, IN_INTER, MEMBER_NOT_EMPTY;
        cases;
        suppose ~Collinear A B C;
        qed     by H1, -, H2, m_line, Ylm, TwosidesTriangle2aLine;
        suppose Collinear A B C     [ABCcol];
          B IN m     [Bm] by -, m_line, notAC, I1, Collinear_DEF;
          ~(Y = A) /\ ~(Y = B) /\ ~(Y = C)     [YnotABC] by Ylm, H2, NOTIN;
          Y NOTIN open (A,B)  \/  Y NOTIN open (A,C)  \/  Y NOTIN open (B,C)     by ABCcol, Interval2sides2aLine;
          A IN ray Y B DELETE Y  \/  A IN ray Y C DELETE Y  \/  B IN ray Y C DELETE Y     by YnotABC, m_line, Bm, Ylm, Collinear_DEF, -, IN_Ray, IN_DELETE;
        qed     by H1, Ylm, H2, -, RaySameSide;
      end;
    end;
  end;
`;;

let FourPointsOrder = thm `;
  let A B C X be point;
  let l be point_set;
  assume Line l /\ A IN l /\ B IN l /\ C IN l /\ X IN l         [H1];
  assume ~(X = A) /\ ~(X = B) /\ ~(X = C)                 [H2];
  assume B IN open (A,C)                                 [H3];
  thus ordered X A B C  \/  ordered A X B C  \/
       ordered A B X C  \/  ordered A B C X

  proof
    A IN open (X,B)  \/  X IN open (A,B)  \/  X IN open (B,C)  \/  C IN open (B,X)
    proof
      ~(A = B) /\ ~(B = C)    [ABCdistinct] by H3, B1';
      Collinear A B X /\ Collinear A C X /\ Collinear C B X     [ACXcol] by H1, Collinear_DEF;
      A IN open (X,B)  \/  X IN open (A,B)  \/  B IN open (A,X)     by H2, ABCdistinct, -, B3', B1';
      cases     by -;
      suppose A IN open (X,B) \/ X IN open (A,B);
      qed     by -;
      suppose B IN open (A,X);
        B NOTIN open (C,X)     by ACXcol, H3, -, Interval2sides2aLine, NOTIN;
      qed     by H2, ABCdistinct, ACXcol, -, B3', B1', NOTIN;
    end;
    qed by -, H3, B1', TransitivityBetweenness, TransitivityBetweennessVariant, Reverse4Order;
`;;

let HilbertAxiomRedundantByMoore = thm `;
  let A B C D be point;
  let l be point_set;
  assume Line l /\ A IN l /\ B IN l /\ C IN l /\ D IN l                         [H1];
  assume ~(A = B) /\ ~(A = C) /\ ~(A = D) /\ ~(B = C) /\ ~(B = D) /\ ~(C = D)        [H2];
  thus ordered D A B C \/ ordered A D B C \/ ordered A B D C \/ ordered A B C D \/
       ordered D A C B \/ ordered A D C B \/ ordered A C D B \/ ordered A C B D \/
       ordered D C A B \/ ordered C D A B \/ ordered C A D B \/ ordered C A B D

  proof
    Collinear A B C     by H1, Collinear_DEF;
    B IN open (A,C)  \/  C IN open (A,B)  \/  A IN open (C,B)     by H2, -, B3', B1';
  qed     by -, H1, H2, FourPointsOrder;
`;;

let InteriorTransitivity = thm `;
  let A O B F G be point;
  assume G IN int_angle A O B     [GintAOB];
  assume F IN int_angle A O G     [FintAOG];
  thus F IN int_angle A O B

  proof
    ~Collinear A O B     [AOBncol] by GintAOB, IN_InteriorAngle;
    consider G' such that
    G' IN open (A,B)  /\  G' IN ray O G DELETE O     [CrossG] by GintAOB, Crossbar_THM;
    F IN int_angle A O G'     by FintAOG, -, InteriorWellDefined;
    consider F' such that
    F' IN open (A,G')  /\  F' IN ray O F DELETE O     [CrossF] by -, Crossbar_THM;
    ~(F' = O) /\ ~(F = O) /\ Collinear O F F' /\ O NOTIN open (F',F)     by -, IN_DELETE, IN_Ray;
    F IN ray O F' DELETE O     [FrOF'] by -, CollinearSymmetry, B1', NOTIN, IN_Ray, IN_DELETE;
    open (A,G') SUBSET open (A,B)  /\  F' IN open (A,B)     by CrossG, IntervalsAreConvex, CrossF, SUBSET;
    F' IN int_angle A O B     by AOBncol, -, ConverseCrossbar;
  qed     by -, FrOF', WholeRayInterior;
`;;

let HalfPlaneConvexNonempty = thm `;
  let l H be point_set;
  let A be point;
  assume Line l /\ A NOTIN l                         [l_line];
  assume H = {X | X NOTIN l  /\  X,A same_side l}            [HalfPlane];
  thus ~(H = {})  /\  H SUBSET complement l  /\  Convex H

  proof
    ! X. X IN H  <=>  X NOTIN l  /\  X,A same_side l     [Hdef] by HalfPlane, SET_RULE;
    H SUBSET complement l     [Hsub] by -, IN_PlaneComplement, SUBSET;
    A,A same_side l  /\  A IN H     by l_line, SameSideReflexive, Hdef;
    ~(H = {})     [Hnonempty] by -, MEMBER_NOT_EMPTY;
    ! P Q X.  P IN H /\ Q IN H /\ X IN open (P,Q)  ==>  X IN H
    proof
      let  P Q X be point;
      assume P IN H /\ Q IN H /\ X IN open (P,Q)     [PXQ];
      P NOTIN l  /\  P,A same_side l  /\  Q NOTIN l  /\  Q,A same_side l     [PQinH] by -, Hdef;
      P,Q same_side l     [Psim_lQ] by l_line, -, SameSideSymmetric, SameSideTransitive;
      X NOTIN l     [notXl] by -, PXQ, SameSide_DEF, NOTIN;
      open (X,P) SUBSET open (P,Q)     by PXQ, IntervalsAreConvex, B1', SUBSET;
      X,P same_side l     by l_line, -, SUBSET, Psim_lQ, SameSide_DEF;
      X,A same_side l     by l_line, notXl, PQinH, -, Psim_lQ, PQinH, SameSideTransitive;
    qed     by -, notXl, Hdef;
    Convex H     by -, SUBSET, CONVEX;
  qed     by Hnonempty, Hsub, -;
`;;

let PlaneSeparation = thm `;
  let l be point_set;
  assume Line l                                                 [l_line];
  thus ? H1 H2:point_set. H1 INTER H2 = {}  /\  ~(H1 = {})  /\  ~(H2 = {})  /\
         Convex H1  /\  Convex H2  /\  complement l = H1 UNION H2  /\
         ! P Q. P IN H1 /\ Q IN H2  ==>  ~(P,Q same_side l)

  proof
    consider A such that
    A NOTIN l     [notAl] by l_line, ExistsPointOffLine;
    consider E such that
    E IN l  /\  ~(A = E)     [El] by l_line, I2, -, NOTIN;
    consider B such that
    E IN open (A,B)  /\  ~(E = B)  /\  Collinear A E B     [AEB] by -, B2', B1';
    B NOTIN l     [notBl] by l_line, El, -, I1, Collinear_DEF, notAl, NOTIN;
    ~(A,B same_side l)     [Ansim_lB] by l_line, El, AEB, SameSide_DEF;
    consider H1 H2 such that
    H1 = {X | X NOTIN l  /\  X,A same_side l}  /\  H2 = {X | X NOTIN l  /\  X,B same_side l}     [H12sets];
    ! X. (X IN H1  <=>  X NOTIN l /\ X,A same_side l) /\ (X IN H2  <=>  X NOTIN l /\ X,B same_side l)     [H12def] by -, SET_RULE;
    ! X. X IN H1  <=>  X NOTIN l  /\  X,A same_side l     [H1def] by H12sets, SET_RULE;
    ! X. X IN H2  <=>  X NOTIN l  /\  X,B same_side l     [H2def] by H12sets, SET_RULE;
    H1 INTER H2 = {}     [H12disjoint]
    proof
      assume ~(H1 INTER H2 = {});
      consider V such that
      V IN H1 /\ V IN H2     by -, MEMBER_NOT_EMPTY, IN_INTER;
      V NOTIN l  /\  V,A same_side l  /\  V NOTIN l  /\  V,B same_side l     by -, H12def;
      A,B same_side l     by l_line, -, notAl, notBl, SameSideSymmetric, SameSideTransitive;
    qed     by -, Ansim_lB;
    ~(H1 = {}) /\ ~(H2 = {}) /\ H1 SUBSET complement l /\ H2 SUBSET complement l /\ Convex H1 /\ Convex H2     [H12convex_nonempty] by l_line, notAl, notBl, H12sets, HalfPlaneConvexNonempty;
    H1 UNION H2  SUBSET  complement l     [H12sub] by H12convex_nonempty, UNION_SUBSET;
    ! C. C IN complement l  ==>  C IN H1 UNION H2
    proof
      let C be point;
      assume C IN complement l;
      C NOTIN l     [notCl] by -, IN_PlaneComplement;
      C,A same_side l  \/  C,B same_side l     by l_line, notAl, notBl, -, Ansim_lB, AtMost2Sides;
      C IN H1  \/  C IN H2     by notCl, -, H12def;
    qed     by -, IN_UNION;
    complement l  SUBSET  H1 UNION H2     by -, SUBSET;
    complement l  =  H1 UNION H2     [compl_H1unionH2] by H12sub, -, SUBSET_ANTISYM;
    ! P Q. P IN H1 /\ Q IN H2  ==>  ~(P,Q same_side l)     [opp_sides]
    proof
      let P Q be point;
      assume P IN H1 /\ Q IN H2;
      P NOTIN l  /\  P,A same_side l  /\   Q NOTIN l  /\  Q,B same_side l     [PH1_QH2] by -, H12def, IN;
    qed     by l_line, -, notAl, SameSideSymmetric, notBl, Ansim_lB, SameSideTransitive;
  qed     by H12disjoint, H12convex_nonempty, compl_H1unionH2, opp_sides;
`;;

let TetralateralSymmetry = thm `;
  let A B C D be point;
  assume Tetralateral A B C D     [H1];
  thus Tetralateral B C D A /\ Tetralateral A B D C

  proof
     ~Collinear A B D /\ ~Collinear B D C /\ ~Collinear D C A /\ ~Collinear C A B      [TetraABCD] by H1, Tetralateral_DEF, CollinearSymmetry;
  qed     by H1, -, Tetralateral_DEF;
`;;

let EasyEmptyIntersectionsTetralateralHelp = thm `;
  let A B C D be point;
  assume Tetralateral A B C D                   [H1];
  thus open (A,B) INTER open (B,C) = {}

  proof
    ! X. X IN open (B,C)  ==>  X NOTIN open (A,B)
    proof
      let X be point;
      assume X IN open (B,C);
      ~Collinear A B C /\ Collinear B X C /\ ~(X = B)     by H1, Tetralateral_DEF, -, B1';
      ~Collinear A X B     by -, CollinearSymmetry, B1', NoncollinearityExtendsToLine;
    qed by -, B1', NOTIN;
  qed by -, DisjointOneNotOther;
`;;

let EasyEmptyIntersectionsTetralateral = thm `;
  let A B C D be point;
  assume Tetralateral A B C D                                           [H1];
  thus open (A,B) INTER open (B,C) = {}  /\  open (B,C) INTER open (C,D) = {}  /\
       open (C,D) INTER open (D,A) = {}  /\  open (D,A) INTER open (A,B) = {}

  proof
    Tetralateral B C D A  /\ Tetralateral C D A B  /\ Tetralateral D A B C by H1, TetralateralSymmetry;
  qed by H1, -, EasyEmptyIntersectionsTetralateralHelp;
`;;

let SegmentSameSideOppositeLine = thm `;
  let A B C D be point;
  let a c be point_set;
  assume Quadrilateral A B C D          [H1];
  assume Line a /\ A IN a /\ B IN a         [a_line];
  assume Line c /\ C IN c /\ D IN c         [c_line];
  thus A,B same_side c  \/  C,D same_side a

  proof
    assume ~(C,D same_side a);     :: prove A,B same_side c
    consider G such that
    G IN a /\ G IN open (C,D)     [CGD] by -, a_line, SameSide_DEF;
    G IN c /\ Collinear G B A     [Gc] by c_line, -, BetweenLinear, a_line, Collinear_DEF;
    ~Collinear B C D  /\  ~Collinear C D A  /\  open (A,B) INTER open (C,D) = {}     [quadABCD] by H1, Quadrilateral_DEF, Tetralateral_DEF;
    A NOTIN c /\ B NOTIN c /\ ~(A = G) /\ ~(B = G)     [Distinct] by -, c_line, Collinear_DEF, NOTIN, Gc;
    G NOTIN open (A,B)     by quadABCD, CGD, DisjointOneNotOther;
    A IN ray G B DELETE G      by Distinct, Gc, -, IN_Ray, IN_DELETE;
  qed     by c_line, Gc, Distinct, -, RaySameSide;
`;;

let ConvexImpliesQuad = thm `;
  let A B C D be point;
  assume Tetralateral A B C D                                   [H1];
  assume C IN int_angle D A B  /\  D IN int_angle A B C            [H2];
  thus Quadrilateral A B C D

  proof
    ~(A = B) /\ ~(B = C) /\ ~(A = D)     [TetraABCD] by H1, Tetralateral_DEF;
    consider a such that
    Line a /\ A IN a /\ B IN a     [a_line] by TetraABCD, I1;
    consider b such that
    Line b /\ B IN b /\ C IN b     [b_line] by TetraABCD, I1;
    consider d such that
    Line d /\ D IN d /\ A IN d     [d_line] by TetraABCD, I1;
    open (B,C) SUBSET b  /\  open (A,B) SUBSET a     [BCbABa] by b_line, a_line, BetweenLinear, SUBSET;
    D,A same_side b  /\  C,D same_side a     by H2, a_line, b_line, d_line, InteriorUse;
    b INTER open (D,A) = {}  /\  a INTER open (C,D) = {}     by -, b_line, SameSide_DEF,  SET_RULE;
    open (B,C) INTER open (D,A) = {}  /\  open (A,B) INTER open (C,D) = {}     by BCbABa, -, SET_RULE;
  qed     by H1, -, Quadrilateral_DEF;
`;;

let DiagonalsIntersectImpliesConvexQuad = thm `;
  let A B C D G be point;
  assume ~Collinear B C D               [BCDncol];
  assume G IN open (A,C)  /\  G IN open (B,D)              [DiagInt];
  thus ConvexQuadrilateral A B C D

  proof
    ~(B = C) /\ ~(B = D) /\ ~(C = D) /\ ~(C = A) /\ ~(A = G) /\ ~(D = G) /\ ~(B = G)     [Distinct] by BCDncol, NonCollinearImpliesDistinct, DiagInt, B1';
    Collinear A G C /\ Collinear B G D     [AGCcol] by DiagInt, B1';
    ~Collinear C D A     [CDAncol] by BCDncol, CollinearSymmetry, Distinct, AGCcol,  NoncollinearityExtendsToLine;
    ~Collinear D A B     [DABncol] by -, CollinearSymmetry, Distinct, AGCcol, NoncollinearityExtendsToLine;
    ~Collinear A B C     [ABCncol] by -, CollinearSymmetry, Distinct, AGCcol, NoncollinearityExtendsToLine;
    ~(A = B) /\ ~(A = D)     by DABncol, NonCollinearImpliesDistinct;
    Tetralateral A B C D     [TetraABCD] by Distinct, -, BCDncol, CDAncol, DABncol, ABCncol, Tetralateral_DEF;
    A IN ray C G DELETE C  /\  B IN ray D G DELETE D  /\  C IN ray A G DELETE A  /\  D IN ray B G DELETE B     [ArCG] by DiagInt, B1', IntervalRayEZ;
    G IN int_angle B C D /\ G IN int_angle C D A /\ G IN int_angle D A B /\ G IN int_angle A B C     by BCDncol, CDAncol, DABncol, ABCncol, DiagInt, B1', ConverseCrossbar;
    A IN int_angle B C D /\ B IN int_angle C D A /\ C IN int_angle D A B /\ D IN int_angle A B C     by -, ArCG, WholeRayInterior;
  qed         by TetraABCD, -, ConvexImpliesQuad, ConvexQuad_DEF;
`;;

let DoubleNotSimImpliesDiagonalsIntersect = thm `;
  let A B C D be point;
  let l m be point_set;
  assume Line l /\ A IN l /\ C IN l         [l_line];
  assume Line m /\ B IN m /\ D IN m         [m_line];
  assume Tetralateral A B C D                   [H1];
  assume ~(B,D same_side l)                     [H2];
  assume ~(A,C same_side m)                     [H3];
  thus (? G. G IN open (A,C) INTER open (B,D)) /\ ConvexQuadrilateral A B C D

  proof
    ~Collinear A B C /\ ~Collinear B C D /\ ~Collinear C D A /\ ~Collinear D A B     [TetraABCD] by H1, Tetralateral_DEF;
    consider G such that
    G IN open (A,C) /\ G IN m     [AGC] by H3, m_line, SameSide_DEF;
    G IN l     [Gl] by l_line, -, BetweenLinear;
    A NOTIN m /\ B NOTIN l /\ D NOTIN l     by TetraABCD, m_line, l_line, Collinear_DEF, NOTIN;
    ~(l = m) /\ B IN m DELETE G /\ D IN m DELETE G     [BDm_G] by -, l_line, NOTIN, m_line, Gl, IN_DELETE;
    l INTER m = {G}     by l_line, m_line, -, Gl, AGC, I1Uniqueness;
    G IN open (B,D)     by l_line, m_line, -, BDm_G, H2, EquivIntersection, NOTIN;
  qed     by AGC, -, IN_INTER, TetraABCD, DiagonalsIntersectImpliesConvexQuad;
`;;

let ConvexQuadImpliesDiagonalsIntersect = thm `;
  let A B C D be point;
  let l m be point_set;
  assume Line l /\ A IN l /\ C IN l                                 [l_line];
  assume Line m /\ B IN m /\ D IN m                                 [m_line];
  assume ConvexQuadrilateral A B C D                                    [ConvQuadABCD];
  thus ~(B,D same_side l) /\ ~(A,C same_side m) /\
       (? G. G IN open (A,C) INTER open (B,D)) /\ ~Quadrilateral A B D C

  proof
    Tetralateral A B C D /\ A IN int_angle B C D /\ D IN int_angle A B C     [convquadABCD] by ConvQuadABCD, ConvexQuad_DEF, Quadrilateral_DEF;
    ~(B,D same_side l)  /\  ~(A,C same_side m)     [opp_sides] by convquadABCD, l_line, m_line, InteriorOpposite;
    consider G such that
    G IN open (A,C) INTER open (B,D)     [Gexists] by l_line, m_line, convquadABCD, opp_sides, DoubleNotSimImpliesDiagonalsIntersect;
    ~(open (B,D) INTER open (C,A) = {})     by -, IN_INTER, B1', MEMBER_NOT_EMPTY;
    ~Quadrilateral A B D C     by -, Quadrilateral_DEF;
  qed     by opp_sides, Gexists, -;
`;;

let FourChoicesTetralateralHelp = thm `;
  let A B C D be point;
  assume Tetralateral A B C D                                   [H1];
  assume C IN int_angle D A B                                    [CintDAB];
  thus ConvexQuadrilateral A B C D \/ C IN int_triangle D A B

  proof
    ~(A = B) /\ ~(D = A) /\ ~(A = C) /\ ~(B = D) /\ ~Collinear A B C /\ ~Collinear B C D /\ ~Collinear C D A /\ ~Collinear D A B     [TetraABCD] by H1, Tetralateral_DEF;
    consider a d such that
    Line a /\ A IN a /\ B IN a  /\
    Line d /\ D IN d /\ A IN d     [ad_line] by TetraABCD, I1;
    consider l m such that
    Line l /\ A IN l /\ C IN l  /\
    Line m /\ B IN m /\ D IN m     [lm_line] by TetraABCD, I1;
    C NOTIN a /\ C NOTIN d /\ B NOTIN l /\ D NOTIN l /\ A NOTIN m /\ C NOTIN m /\ ~Collinear A B D /\ ~Collinear B D A          [tetra'] by TetraABCD, ad_line, lm_line, Collinear_DEF, NOTIN, CollinearSymmetry;
    ~(B,D same_side l)     [Bsim_lD] by CintDAB, lm_line, InteriorOpposite, -, SameSideSymmetric;
    cases;
    suppose ~(A,C same_side m);
    qed     by lm_line, H1, Bsim_lD, -, DoubleNotSimImpliesDiagonalsIntersect;
    suppose A,C same_side m;
      C,A same_side m     [Csim_mA] by lm_line, -, tetra', SameSideSymmetric;
      C,B same_side d  /\  C,D same_side a     by ad_line, CintDAB, InteriorUse;
      C IN int_angle A B D  /\  C IN int_angle B D A     by tetra', ad_line, lm_line, Csim_mA, -, IN_InteriorAngle;
      C IN int_triangle D A B     by CintDAB, -, IN_InteriorTriangle;
    qed     by -;
  end;
`;;

let InteriorTriangleSymmetry = thm `;
  ! A B C P. P IN int_triangle A B C  ==> P IN int_triangle B C A
  by IN_InteriorTriangle;
`;;

let FourChoicesTetralateral = thm `;
  let A B C D be point;
  let a be point_set;
  assume Tetralateral A B C D                   [H1];
  assume Line a /\ A IN a /\ B IN a                 [a_line];
  assume C,D same_side a                        [Csim_aD];
  thus ConvexQuadrilateral A B C D  \/  ConvexQuadrilateral A B D C  \/
       D IN int_triangle A B C  \/  C IN int_triangle D A B

  proof
     ~(A = B) /\ ~Collinear A B C /\ ~Collinear C D A /\ ~Collinear D A B /\ Tetralateral A B D C     [TetraABCD] by H1, Tetralateral_DEF, TetralateralSymmetry;
    ~Collinear C A D /\ C NOTIN a /\ D NOTIN a     [notCDa] by TetraABCD, CollinearSymmetry, a_line, Collinear_DEF, NOTIN;
    C IN int_angle D A B  \/  D IN int_angle C A B     by TetraABCD, a_line, -, Csim_aD, AngleOrdering;
    cases     by -;
    suppose C IN int_angle D A B;
      ConvexQuadrilateral A B C D  \/  C IN int_triangle D A B     by H1, -, FourChoicesTetralateralHelp;
    qed     by -;
    suppose D IN int_angle C A B;
      ConvexQuadrilateral A B D C  \/  D IN int_triangle C A B     by TetraABCD, -, FourChoicesTetralateralHelp;
    qed     by -, InteriorTriangleSymmetry;
  end;
`;;

let QuadrilateralSymmetry = thm `;
  ! A B C D:point. Quadrilateral A B C D  ==>
  Quadrilateral B C D A  /\  Quadrilateral C D A B  /\  Quadrilateral D A B C
  by Quadrilateral_DEF, INTER_COMM, TetralateralSymmetry, Quadrilateral_DEF;
`;;

let FiveChoicesQuadrilateral = thm `;
  let A B C D be point;
  let l m be point_set;
  assume Quadrilateral A B C D                                                  [H1];
  assume Line l /\ A IN l /\ C IN l  /\  Line m /\ B IN m /\ D IN m                                              [lm_line];
  thus (ConvexQuadrilateral A B C D  \/  A IN int_triangle B C D  \/
  B IN int_triangle C D A  \/  C IN int_triangle D A B  \/  D IN int_triangle A B C)  /\
  (~(B,D same_side l) \/ ~(A,C same_side m))

  proof
    Tetralateral A B C D     [H1Tetra] by H1, Quadrilateral_DEF;
    ~(A = B) /\ ~(A = D) /\ ~(B = C) /\ ~(C = D)     [Distinct] by H1Tetra, Tetralateral_DEF;
    consider a c such that
    Line a /\ A IN a /\ B IN a  /\
    Line c /\ C IN c /\ D IN c     [ac_line] by Distinct, I1;
    Quadrilateral C D A B  /\  Tetralateral C D A B     [tetraCDAB] by H1, QuadrilateralSymmetry, Quadrilateral_DEF;
    ~ConvexQuadrilateral A B D C  /\  ~ConvexQuadrilateral C D B A     [notconvquad] by Distinct, I1, H1, -, ConvexQuadImpliesDiagonalsIntersect;
    ConvexQuadrilateral A B C D  \/  A IN int_triangle B C D  \/
    B IN int_triangle C D A  \/  C IN int_triangle D A B  \/  D IN int_triangle A B C     [5choices]
    proof
      A,B same_side c  \/  C,D same_side a     by H1, ac_line, SegmentSameSideOppositeLine;
      cases     by -;
      suppose C,D same_side a;
      qed     by H1Tetra, ac_line, -, notconvquad, FourChoicesTetralateral;
      suppose A,B same_side c;
        ConvexQuadrilateral C D A B  \/  B IN int_triangle C D A  \/  A IN int_triangle B C D     [X1] by tetraCDAB, ac_line, -, notconvquad, FourChoicesTetralateral;
      qed     by -, QuadrilateralSymmetry, ConvexQuad_DEF;
    end;
    ~(B,D same_side l) \/ ~(A,C same_side m)     by -, lm_line, ConvexQuadImpliesDiagonalsIntersect, IN_InteriorTriangle, InteriorAngleSymmetry, InteriorOpposite;
  qed     by 5choices, -;
`;;

let IntervalSymmetry = thm `;
  ! A B: point. open (A,B) = open (B,A)
  by B1', EXTENSION;
`;;

let SegmentSymmetry = thm `;
  ! A B: point. seg A B = seg B A
  by Segment_DEF, IntervalSymmetry, SET_RULE;
`;;

let C1OppositeRay = thm `;
  let O P be point;
  let s be point_set;
  assume Segment s /\ ~(O = P)                   [H1];
  thus ? Q. P IN open (O,Q)  /\  seg P Q === s

  proof
    consider Z such that
    P IN open (O,Z)  /\  ~(P = Z)     [OPZ] by H1, B2', B1';
    consider Q such that
    Q IN ray P Z DELETE P /\ seg P Q === s     [PQeq] by H1, -, C1;
    P IN open (Q,O)     by OPZ, -, OppositeRaysIntersect1pointHelp;
  qed     by -, B1', PQeq;
`;;

let OrderedCongruentSegments = thm `;
  let A B C D F be point;
  assume ~(A = C) /\ ~(D = F)                            [H1];
  assume seg A C === seg D F                              [H2];
  assume B IN open (A,C)                                 [H3];
  thus ? E. E IN open (D,F)  /\  seg A B === seg D E

  proof
    Segment (seg A B) /\ Segment (seg A C) /\ Segment (seg B C) /\ Segment (seg D F)     [segs] by H3, B1', H1, SEGMENT;
    seg D F === seg A C     [DFeqAC] by -, H2, C2Symmetric;
    consider E such that
    E IN ray D F DELETE D /\ seg D E === seg A B     [DEeqAB] by segs, H1, C1;
    ~(E = D) /\ Collinear D E F /\ D NOTIN open (F,E)     [ErDF] by -, IN_DELETE, IN_Ray, B1', CollinearSymmetry, NOTIN;
    consider F' such that
    E IN open (D,F') /\ seg E F' === seg B C     [DEF'] by segs, -, C1OppositeRay;
    seg D F' === seg A C     [DF'eqAC] by DEF', H3, DEeqAB, C3;
    Segment (seg D F') /\ Segment (seg D E)     by DEF', B1', SEGMENT;
    seg A C === seg D F' /\ seg A B === seg D E     [ABeqDE] by segs, -, DF'eqAC, C2Symmetric, DEeqAB;
    F' IN ray D E DELETE D  /\  F IN ray D E DELETE D     by DEF', IntervalRayEZ, ErDF, IN_Ray, H1, IN_DELETE;
    F' = F     by ErDF, segs, -, DF'eqAC, DFeqAC, C1;
  qed     by -, DEF', ABeqDE;
`;;

let SegmentSubtraction = thm `;
  let A B C A' B' C' be point;
  assume B IN open (A,C)  /\  B' IN open (A',C')           [H1];
  assume seg A B === seg A' B'                            [H2];
  assume seg A C === seg A' C'                            [H3];
  thus seg B C === seg B' C'

  proof
    ~(A = B) /\ ~(A = C) /\ Collinear A B C /\ Segment (seg A' C') /\ Segment (seg B' C')     [Distinct] by H1, B1', SEGMENT;
    consider Q such that
    B IN open (A,Q)  /\  seg B Q === seg B' C'     [defQ] by -, C1OppositeRay;
    seg A Q === seg A' C'     [AQ_A'C'] by H1, H2, -, C3;
    ~(A = Q)  /\  Collinear A B Q  /\  A NOTIN open (C,B)  /\  A NOTIN open (Q,B)     by defQ, B1', H1, B3', NOTIN;
    C IN ray A B DELETE A  /\  Q IN ray A B DELETE A     by Distinct, -, IN_Ray, IN_DELETE;
    C = Q     by Distinct, -, AQ_A'C', H3, C1;
  qed     by defQ, -;
`;;

let SegmentOrderingUse = thm `;
  let A B be point;
  let s be point_set;
  assume Segment s  /\  ~(A = B)                 [H1];
  assume s <__ seg A B                          [H2];
  thus ? G. G IN open (A,B)  /\  s === seg A G

  proof
    consider A' B' G' such that
    seg A B = seg A' B'  /\  G' IN open (A',B')  /\  s === seg A' G'     [H2'] by H2, SegmentOrdering_DEF;
    ~(A' = G') /\ ~(A' = B')  /\  seg A' B' === seg A B     [A'notB'G'] by -, B1', H1, SEGMENT, C2Reflexive;
    consider G such that
    G IN open (A,B)  /\  seg A' G' === seg A G     [AGB] by A'notB'G', H1, H2', -,  OrderedCongruentSegments;
    s === seg A G     by H1, A'notB'G', -, B1', SEGMENT, H2', C2Transitive;
  qed     by AGB, -;
`;;

let SegmentTrichotomy1 = thm `;
  let s t be point_set;
  assume s <__ t                        [H1];
  thus ~(s === t)

  proof
    consider A B G such that
    Segment s /\ t = seg A B /\ G IN open (A,B) /\ s === seg A G     [H1'] by H1, SegmentOrdering_DEF;
    ~(A = G) /\ ~(A = B) /\ ~(G = B)     [Distinct] by H1', B1';
    seg A B === seg A B     [ABrefl] by -, SEGMENT, C2Reflexive;
    G IN ray A B DELETE A  /\  B IN ray A B DELETE A     by H1', IntervalRay, EndpointInRay, Distinct, IN_DELETE;
    ~(seg A G === seg A B)  /\ seg A G === s     by Distinct, SEGMENT, -, ABrefl, C1, H1', C2Symmetric;
  qed     by Distinct, H1', SEGMENT, -, C2Transitive;
`;;

let SegmentTrichotomy2 = thm `;
  let s t u be point_set;
  assume s <__ t                                [H1];
  assume Segment u  /\  t === u                    [H2];
  thus s <__ u

  proof
    consider A B P such that
    Segment s  /\  t = seg A B  /\  P IN open (A,B)  /\  s === seg A P     [H1'] by H1, SegmentOrdering_DEF;
    ~(A = B) /\ ~(A = P)     [Distinct] by -, B1';
    consider X Y such that
    u = seg X Y /\ ~(X = Y)     [uXY] by H2, SEGMENT;
    consider Q such that
    Q IN open (X,Y)  /\  seg A P === seg X Q     [XQY] by Distinct, -, H1', H2, OrderedCongruentSegments;
    ~(X = Q)  /\  s === seg X Q     by -, B1', H1', Distinct, SEGMENT, XQY, C2Transitive;
  qed     by H1', uXY, XQY, -, SegmentOrdering_DEF;
`;;

let SegmentOrderTransitivity = thm `;
  let s t u be point_set;
  assume s <__ t  /\  t <__ u            [H1];
  thus s <__ u

  proof
    consider A B G such that
    u = seg A B  /\  G IN open (A,B)  /\  t === seg A G     [H1'] by H1, SegmentOrdering_DEF;
    ~(A = B) /\ ~(A = G) /\ Segment s     [Distinct] by H1',  B1', H1, SegmentOrdering_DEF;
    s <__ seg A G     by H1, H1', Distinct, SEGMENT, SegmentTrichotomy2;
    consider F such that
    F IN open (A,G) /\ s === seg A F     [AFG] by Distinct, -, SegmentOrderingUse;
    F IN open (A,B)     by H1', IntervalsAreConvex, -, SUBSET;
  qed     by Distinct, H1', -, AFG, SegmentOrdering_DEF;
`;;

let SegmentTrichotomy = thm `;
  let s t be point_set;
  assume Segment s /\ Segment t                          [H1];
  thus (s === t  \/  s <__ t  \/  t <__ s)  /\  ~(s === t /\ s <__ t)  /\
       ~(s === t /\ t <__ s)  /\  ~(s <__ t /\ t <__ s)

  proof
    ~(s === t  /\  s <__ t)     [Not12]
    proof
      assume s <__ t;
    qed by -, SegmentTrichotomy1;
    ~(s === t  /\  t <__ s)     [Not13]
    proof
      assume t <__ s;
      ~(t === s) by -, SegmentTrichotomy1;
    qed by H1, -, C2Symmetric;
    ~(s <__ t  /\  t <__ s)     [Not23]
    proof
      assume s <__ t  /\  t <__ s;
      s <__ s     by H1, -, SegmentOrderTransitivity;
    qed     by -, SegmentTrichotomy1, H1, C2Reflexive;
    consider O P such that
    s = seg O P  /\  ~(O = P)     [sOP] by H1, SEGMENT;
    consider Q such that
    Q IN ray O P DELETE O  /\  seg O Q === t     [QrOP] by H1, -, C1;
    O NOTIN open (Q,P)  /\  Collinear O P Q   /\  ~(O = Q)     [notQOP] by -, IN_DELETE, IN_Ray;
    s === seg O P  /\  t === seg O Q  /\  seg O Q === t  /\  seg O P === s     [stOPQ] by H1, sOP, -, SEGMENT, QrOP, C2Reflexive, C2Symmetric;
    cases;
    suppose Q = P;
      s === t     by -, sOP, QrOP;
    qed     by -, Not12, Not13, Not23;
    suppose ~(Q = P);
      P IN open (O,Q)  \/  Q IN open (O,P)     by sOP, -, notQOP, B3', B1', NOTIN;
      s <__ seg O Q  \/  t <__ seg O P     by H1, -, stOPQ, SegmentOrdering_DEF;
      s <__ t  \/  t <__ s     by -, H1, stOPQ, SegmentTrichotomy2;
    qed     by -, Not12, Not13, Not23;
  end;
`;;

let C4Uniqueness = thm `;
  let O A B P be point;
  let l be point_set;
  assume Line l /\ O IN l /\ A IN l /\ ~(O = A)     [H1];
  assume B NOTIN l /\ P NOTIN l /\ P,B same_side l       [H2];
  assume angle A O P === angle A O B             [H3];
  thus ray O B = ray O P

  proof
    ~(O = B) /\ ~(O = P) /\ Ray (ray O B) /\ Ray (ray O P)     [Distinct] by H2, H1, NOTIN, RAY;
    ~Collinear A O B  /\  B,B same_side l     [Bsim_lB] by H1, H2, I1, Collinear_DEF, NOTIN, SameSideReflexive;
    Angle (angle A O B)  /\  angle A O B === angle A O B     by -, ANGLE, C5Reflexive;
  qed     by -, H1, H2, Distinct, Bsim_lB, H3, C4;
`;;

let AngleSymmetry = thm `;
  ! A O B. angle A O B = angle B O A
  by Angle_DEF, UNION_COMM;
`;;

let TriangleCongSymmetry = thm `;
  let A B C A' B' C' be point;
  assume A,B,C cong A',B',C'                                       [H1];
  thus A,C,B cong A',C',B' /\ B,A,C cong B',A',C' /\
       B,C,A cong B',C',A' /\ C,A,B cong C',A',B' /\ C,B,A cong C',B',A'

  proof
    ~Collinear A B C /\ ~Collinear A' B' C' /\
    seg A B === seg A' B' /\ seg A C === seg A' C' /\ seg B C === seg B' C' /\
    angle A B C === angle A' B' C' /\ angle B C A === angle B' C' A' /\ angle C A B === angle C' A' B'    [H1'] by H1, TriangleCong_DEF;
    seg B A === seg B' A' /\ seg C A === seg C' A' /\ seg C B === seg C' B'     [segments] by H1', SegmentSymmetry;
    angle C B A === angle C' B' A' /\ angle A C B === angle A' C' B' /\ angle B A C === angle B' A' C'     by H1', AngleSymmetry;
  qed by CollinearSymmetry, H1', segments, -, TriangleCong_DEF;
`;;

let SAS = thm `;
  let A B C A' B' C' be point;
  assume ~Collinear A B C /\ ~Collinear A' B' C'         [H1];
  assume seg B A === seg B' A'  /\  seg B C === seg B' C'            [H2];
  assume angle A B C === angle A' B' C'                           [H3];
  thus A,B,C cong A',B',C'

  proof
    ~(A = B) /\ ~(A = C) /\ ~(A' = C')     [Distinct] by H1, NonCollinearImpliesDistinct; :: 134
    consider c such that
    Line c /\ A IN c /\ B IN c     [c_line] by Distinct, I1;
    C NOTIN c     [notCc] by H1, c_line, Collinear_DEF, NOTIN;
    angle B C A === angle B' C' A'     [BCAeq] by H1, H2, H3, C6;
    angle B A C === angle B' A' C'     [BACeq] by H1, CollinearSymmetry, H2, H3, AngleSymmetry, C6;
    consider Y such that
    Y IN ray A C DELETE A  /\  seg A Y === seg A' C'     [YrAC] by Distinct, SEGMENT, C1;
    Y NOTIN c  /\  Y,C same_side c     [Ysim_cC] by c_line, notCc, -, RaySameSide;
    ~Collinear Y A B     [YABncol] by c_line, -, Distinct, I1, Collinear_DEF, NOTIN;
    ray A Y = ray A C  /\  angle Y A B = angle C A B     by Distinct, YrAC, RayWellDefined, Angle_DEF;
    angle Y A B === angle C' A' B'     by BACeq, -, AngleSymmetry;
    angle A B Y === angle A' B' C'     [ABYeq] by YABncol, H1, CollinearSymmetry, H2, SegmentSymmetry, YrAC, -, C6;
    Angle (angle A B C) /\ Angle (angle A' B' C') /\ Angle (angle A B Y)     by H1, CollinearSymmetry, YABncol, ANGLE;
    angle A B Y === angle A B C     [ABYeqABC] by -, ABYeq, -, H3, C5Symmetric, C5Transitive;
    ray B C = ray B Y  /\  ~(Y = B)  /\  Y IN ray B C     by c_line, Distinct, notCc, Ysim_cC, ABYeqABC, C4Uniqueness, NOTIN, -, EndpointInRay;
    Collinear B C Y  /\  Collinear A C Y     by -, YrAC, IN_DELETE, IN_Ray;
    C = Y     by -, I1, Collinear_DEF, H1;
    seg A C === seg A' C'     by -, YrAC;
  qed     by H1, H2, SegmentSymmetry, -, H3, BCAeq, BACeq, AngleSymmetry, TriangleCong_DEF;
`;;

let ASA = thm `;
  let A B C A' B' C' be point;
  assume ~Collinear A B C /\ ~Collinear A' B' C'         [H1];
  assume seg A C === seg A' C'                                    [H2];
  assume angle C A B === angle C' A' B'  /\  angle B C A === angle B' C' A'          [H3];
  thus A,B,C cong A',B',C'

  proof
    ~(A = B) /\ ~(A = C) /\ ~(B = C) /\ ~(A' = B') /\ ~(A' = C') /\ ~(B' = C') /\ Segment (seg C' B')     [Distinct] by H1, NonCollinearImpliesDistinct, SEGMENT;
    consider D such that
    D IN ray C B DELETE C  /\  seg C D === seg C' B'  /\  ~(D = C)     [DrCB] by -, C1, IN_DELETE;
    Collinear C B D     [CBDcol] by -, IN_DELETE, IN_Ray;
    ~Collinear D C A /\ Angle (angle C A D) /\ Angle (angle C' A' B') /\ Angle (angle C A B)     [DCAncol] by H1, CollinearSymmetry, -, DrCB, NoncollinearityExtendsToLine, H1, ANGLE;
    consider b such that
    Line b /\ A IN b /\ C IN b     [b_line] by Distinct, I1;
    B NOTIN b /\ ~(D = A)     [notBb] by H1, -, Collinear_DEF, NOTIN, DCAncol, NonCollinearImpliesDistinct;
    D NOTIN b  /\  D,B same_side b     [Dsim_bB] by b_line, -, DrCB, RaySameSide;
    ray C D = ray C B     by Distinct, DrCB, RayWellDefined;
    angle D C A === angle B' C' A'     by H3, -, Angle_DEF;
    D,C,A cong B',C',A'     by DCAncol, H1, CollinearSymmetry, DrCB, H2, SegmentSymmetry, -, SAS;
    angle C A D === angle C' A' B'     by -, TriangleCong_DEF;
    angle C A D === angle C A B     by DCAncol, -, H3, C5Symmetric, C5Transitive;
    ray A B = ray A D  /\  D IN ray A B     by b_line, Distinct, notBb, Dsim_bB, -, C4Uniqueness, notBb, EndpointInRay;
    Collinear A B D     by -, IN_Ray;
    D = B     by I1, -, Collinear_DEF, CBDcol, H1;
    seg C B === seg C' B'     by -, DrCB;
    B,C,A cong B',C',A'     by H1, CollinearSymmetry, -, H2, SegmentSymmetry, H3, SAS;
  qed     by -, TriangleCongSymmetry;
`;;

let AngleSubtraction = thm `;
  let A O B A' O' B' G G' be point;
  assume G IN int_angle A O B  /\  G' IN int_angle A' O' B'        [H1];
  assume angle A O B === angle A' O' B'  /\  angle A O G === angle A' O' G'  [H2];
  thus angle G O B === angle G' O' B'

  proof
    ~Collinear A O B /\ ~Collinear A' O' B'     [A'O'B'ncol] by H1, IN_InteriorAngle;
    ~(A = O) /\ ~(O = B) /\ ~(G = O) /\ ~(G' = O') /\ Segment (seg O' A') /\ Segment (seg O' B')     [Distinct] by -, NonCollinearImpliesDistinct, H1, InteriorEZHelp, SEGMENT;
   consider X Y such that
   X IN ray O A DELETE O  /\  seg O X === seg O' A'  /\  Y IN ray O B DELETE O  /\  seg O Y === seg O' B'     [XYexists] by -, C1;
    G IN int_angle X O Y     [GintXOY] by H1, XYexists, InteriorWellDefined, InteriorAngleSymmetry;
    consider H H' such that
    H IN open (X,Y)  /\  H IN ray O G DELETE O  /\
    H' IN open (A',B')  /\  H' IN ray O' G' DELETE O'     [Hexists] by -, H1, Crossbar_THM;
    H IN int_angle X O Y  /\  H' IN int_angle A' O' B'     [HintXOY] by GintXOY, H1, -, WholeRayInterior;
    ray O X = ray O A  /\  ray O Y = ray O B  /\  ray O H = ray O G  /\  ray O' H' = ray O' G'     [Orays] by Distinct, XYexists, Hexists, RayWellDefined;
    angle X O Y === angle A' O' B'  /\  angle X O H === angle A' O' H'     [H2'] by H2, -, Angle_DEF;
    ~Collinear X O Y     by GintXOY, IN_InteriorAngle;
    X,O,Y cong A',O',B'     by -, A'O'B'ncol, H2', XYexists, SAS;
    seg X Y === seg A' B'  /\  angle O Y X === angle O' B' A'  /\  angle Y X O === angle B' A' O'     [XOYcong] by -, TriangleCong_DEF;
    ~Collinear O H X /\ ~Collinear O' H' A' /\ ~Collinear O Y H /\ ~Collinear O' B' H'     [OHXncol] by HintXOY, InteriorEZHelp, InteriorAngleSymmetry, CollinearSymmetry;
    ray X H = ray X Y  /\  ray A' H' = ray A' B'  /\  ray Y H = ray Y X  /\  ray B' H' = ray B' A'     [Hrays] by Hexists, B1', IntervalRay;
    angle H X O === angle H' A' O'     by XOYcong, -, Angle_DEF;
    O,H,X cong O',H',A'     by OHXncol, XYexists, -, H2', ASA;
    seg X H === seg A' H'     by -, TriangleCong_DEF, SegmentSymmetry;
    seg H Y === seg H' B'     by Hexists, XOYcong, -, SegmentSubtraction;
    seg Y O  === seg B' O'  /\  seg Y H === seg B' H'     [YHeq] by XYexists, -, SegmentSymmetry;
    angle O Y H === angle O' B' H'     by XOYcong, Hrays, Angle_DEF;
    O,Y,H cong O',B',H'     by OHXncol, YHeq, -, SAS;
  angle H O Y === angle H' O' B'     by -, TriangleCong_DEF;
  qed     by -, Orays, Angle_DEF;
`;;

let OrderedCongruentAngles = thm `;
  let A O B A' O' B' G be point;
  assume ~Collinear A' O' B'                                    [H1];
  assume angle A O B === angle A' O' B'                           [H2];
  assume G IN int_angle A O B                                    [H3];
  thus ? G'. G' IN int_angle A' O' B'  /\  angle A O G === angle A' O' G'

  proof
    ~Collinear A O B     [AOBncol] by H3, IN_InteriorAngle;
    ~(A = O) /\ ~(O = B) /\ ~(A' = B') /\ ~(O = G) /\ Segment (seg O' A') /\ Segment (seg O' B')     [Distinct] by AOBncol, H1, NonCollinearImpliesDistinct, H3, InteriorEZHelp, SEGMENT;
    consider X Y such that
    X IN ray O A DELETE O  /\  seg O X === seg O' A'  /\  Y IN ray O B DELETE O  /\  seg O Y === seg O' B'     [defXY] by -, C1;
    G IN int_angle X O Y     [GintXOY] by H3, -, InteriorWellDefined, InteriorAngleSymmetry;
    ~Collinear X O Y /\ ~(X = Y)     [XOYncol] by -, IN_InteriorAngle, NonCollinearImpliesDistinct;
    consider H such that
    H IN open (X,Y)  /\  H IN ray O G DELETE O     [defH] by GintXOY, Crossbar_THM;
    ray O X = ray O A  /\  ray O Y = ray O B  /\  ray O H = ray O G     [Orays] by Distinct, defXY, -, RayWellDefined;
    angle X O Y === angle A' O' B'     by H2, -, Angle_DEF;
    X,O,Y cong A',O',B'     by XOYncol, H1, defXY, -, SAS;
    seg X Y === seg A' B'  /\  angle O X Y === angle O' A' B'     [YXOcong] by -, TriangleCong_DEF, AngleSymmetry;
    consider G' such that
    G' IN open (A',B')  /\  seg X H === seg A' G'     [A'G'B'] by XOYncol, Distinct, -, defH, OrderedCongruentSegments;
    G' IN int_angle A' O' B'     [G'intA'O'B'] by H1, -, ConverseCrossbar;
    ray X H = ray X Y  /\  ray A' G' = ray A' B'     by defH, A'G'B', IntervalRay;
    angle O X H === angle O' A' G'     [HXOeq] by -, Angle_DEF, YXOcong;
    H IN int_angle X O Y     by GintXOY, defH, WholeRayInterior;
    ~Collinear O X H /\ ~Collinear O' A' G'     by -, G'intA'O'B', InteriorEZHelp, CollinearSymmetry;
    O,X,H cong O',A',G'     by -, A'G'B', defXY, SegmentSymmetry, HXOeq, SAS;
    angle X O H === angle A' O' G'     by -, TriangleCong_DEF, AngleSymmetry;
    angle A O G === angle A' O' G'     by -, Orays, Angle_DEF;
  qed     by G'intA'O'B', -;
`;;

let AngleAddition = thm `;
  let A O B A' O' B' G G' be point;
  assume G IN int_angle A O B  /\  G' IN int_angle A' O' B'                [H1];
  assume angle A O G === angle A' O' G'  /\  angle G O B === angle G' O' B'          [H2];
  thus angle A O B === angle A' O' B'

  proof
    ~Collinear A O B /\ ~Collinear A' O' B'     [AOBncol] by H1, IN_InteriorAngle;
    ~(A = O) /\ ~(A = B) /\ ~(O = B) /\ ~(A' = O') /\ ~(A' = B') /\ ~(O' = B') /\ ~(G = O)     [Distinct] by -, NonCollinearImpliesDistinct, H1, InteriorEZHelp;
    consider a b such that
    Line a /\ O IN a /\ A IN a  /\
    Line b /\ O IN b /\ B IN b     [a_line] by Distinct, I1;
    consider g such that
    Line g /\ O IN g /\ G IN g     [g_line] by  Distinct, I1;
    G NOTIN a /\ G,B same_side a     [H1'] by a_line, H1, InteriorUse;
    ~Collinear A O G /\ ~Collinear A' O' G'     [AOGncol] by H1, InteriorEZHelp, IN_InteriorAngle;
    Angle (angle A O B) /\ Angle (angle A' O' B') /\ Angle (angle A O G) /\ Angle (angle A' O' G')     [angles] by AOBncol, -, ANGLE;
    ?! r. Ray r /\ ? X. ~(O = X) /\ r = ray O X /\ X NOTIN a /\ X,G same_side a /\ angle A O X === angle A' O' B'     by -, Distinct, a_line, H1', C4;
    consider X such that
    X NOTIN a /\ X,G same_side a /\ angle A O X === angle A' O' B'     [Xexists] by -;
    ~Collinear A O X     [AOXncol] by -, a_line, Distinct, I1, Collinear_DEF, NOTIN;
    angle A' O' B' === angle A O X     by -, AOBncol, ANGLE, Xexists, C5Symmetric;
    consider Y such that
    Y IN int_angle A O X  /\  angle A' O' G' === angle A O Y     [YintAOX] by AOXncol, -, H1, OrderedCongruentAngles;
    ~Collinear A O Y     by -, InteriorEZHelp;
    angle A O Y  === angle A O G     [AOGeq] by -, angles, -, ANGLE, YintAOX, H2, C5Transitive, C5Symmetric;
    consider x such that
    Line x /\ O IN x /\ X IN x     by Distinct, I1;
    Y NOTIN a /\ Y,X same_side a     by a_line, -, YintAOX, InteriorUse;
    Y NOTIN a /\ Y,G same_side a     by  a_line, -, Xexists, H1', SameSideTransitive;
    ray O G = ray O Y     by a_line, Distinct, H1', -, AOGeq, C4Uniqueness;
    G IN ray O Y DELETE O     by Distinct, -, EndpointInRay, IN_DELETE;
    G IN int_angle A O X     [GintAOX] by YintAOX, -, WholeRayInterior;
    angle G O X === angle G' O' B'     [GOXeq] by -, H1, Xexists, H2, AngleSubtraction;
    ~Collinear G O X /\ ~Collinear G O B /\ ~Collinear G' O' B'     [GOXncol] by GintAOX, H1, InteriorAngleSymmetry, InteriorEZHelp, CollinearSymmetry;
    Angle (angle G O X) /\ Angle (angle G O B) /\ Angle (angle G' O' B')     by -, ANGLE;
    angle G O X === angle G O B     [G'O'Xeq] by  angles, -, GOXeq, C5Symmetric, H2, C5Transitive;
    ~(A,X same_side g) /\ ~(A,B same_side g)     [Ansim_aXB] by g_line, GintAOX, H1, InteriorOpposite;
    A NOTIN g /\ B NOTIN g /\ X NOTIN g     [notABXg] by g_line, AOGncol, GOXncol, Distinct, I1, Collinear_DEF, NOTIN;
    X,B same_side g     by g_line, -, Ansim_aXB, AtMost2Sides;
    ray O X = ray O B     by g_line, Distinct, notABXg, -, G'O'Xeq, C4Uniqueness;
  qed     by -, Xexists, Angle_DEF;
`;;

let AngleOrderingUse = thm `;
  let A O B be point;
  let alpha be point_set;
  assume Angle alpha  /\  ~Collinear A O B                   [H1];
  assume alpha <_ang angle A O B                                [H3];
  thus ? G. G IN int_angle A O B /\ alpha === angle A O G

  proof
    consider A' O' B' G' such that
    ~Collinear A' O' B'  /\  angle A O B = angle A' O' B'  /\  G' IN int_angle A' O' B'  /\  alpha === angle A' O' G'     [H3'] by H3, AngleOrdering_DEF;
    Angle (angle A O B) /\ Angle (angle A' O' B') /\ Angle (angle A' O' G')     [angles] by H1, -, ANGLE, InteriorEZHelp;
    angle A' O' B' === angle A O B     by -, H3', C5Reflexive;
    consider G such that
    G IN int_angle A O B  /\  angle A' O' G' === angle A O G     [GintAOB] by H1, H3', -,  OrderedCongruentAngles;
    alpha === angle A O G     by H1, angles, -, InteriorEZHelp, ANGLE, H3', GintAOB, C5Transitive;
  qed     by -, GintAOB;
`;;

let AngleTrichotomy1 = thm `;
  let alpha beta be point_set;
  assume alpha <_ang beta              [H1];
  thus ~(alpha === beta)

  proof
    assume alpha === beta [Con];
    consider A O B G such that
    Angle alpha /\ ~Collinear A O B /\ beta = angle A O B /\ G IN int_angle A O B /\ alpha === angle A O G     [H1'] by H1, AngleOrdering_DEF;
    ~(A = O) /\ ~(O = B) /\ ~Collinear A O G     [Distinct] by H1', NonCollinearImpliesDistinct, InteriorEZHelp;
    consider a such that
    Line a /\ O IN a /\ A IN a     [a_line] by Distinct, I1;
    consider b such that
    Line b /\ O IN b /\ B IN b     [b_line] by Distinct, I1;
    B NOTIN a     [notBa] by a_line, H1', Collinear_DEF, NOTIN;
    G NOTIN a /\ G NOTIN b /\ G,B same_side a     [GintAOB] by a_line, b_line, H1', InteriorUse;
    angle A O G === alpha     by H1', Distinct, ANGLE, C5Symmetric;
    angle A O G === angle A O B     by H1', Distinct, ANGLE, -, Con, C5Transitive;
    ray O B = ray O G     by a_line, Distinct, notBa, GintAOB, -, C4Uniqueness;
    G IN b     by Distinct, -, EndpointInRay, b_line, RayLine, SUBSET;
  qed     by -, GintAOB, NOTIN;
`;;

let AngleTrichotomy2 = thm `;
  let alpha beta gamma be point_set;
  assume alpha <_ang beta              [H1];
  assume Angle gamma                [H2];
  assume beta === gamma                  [H3];
  thus alpha <_ang gamma

  proof
    consider A O B G such that
    Angle alpha /\ ~Collinear A O B /\ beta = angle A O B /\ G IN int_angle A O B /\ alpha === angle A O G     [H1'] by H1, AngleOrdering_DEF;
    consider A' O' B' such that
    gamma = angle A' O' B' /\ ~Collinear A' O' B'     [gammaA'O'B'] by H2, ANGLE;
    consider G' such that
    G' IN int_angle A' O' B' /\ angle A O G === angle A' O' G'     [G'intA'O'B'] by gammaA'O'B', H1', H3,  OrderedCongruentAngles;
    ~Collinear A O G /\ ~Collinear A' O' G'     [ncol] by H1', -, InteriorEZHelp;
    alpha === angle A' O' G'     by H1', ANGLE, -, G'intA'O'B', C5Transitive;
  qed     by H1', -, ncol, gammaA'O'B', G'intA'O'B', -, AngleOrdering_DEF;
`;;

let AngleOrderTransitivity = thm `;
  let alpha beta gamma be point_set;
    assume alpha <_ang beta [H0];
    assume beta <_ang gamma [H2];
    thus alpha <_ang gamma

  proof
    consider A O B G such that
    Angle beta /\ ~Collinear A O B /\ gamma = angle A O B /\ G IN int_angle A O B /\ beta === angle A O G     [H2'] by H2, AngleOrdering_DEF;
    ~Collinear A O G     [AOGncol] by H2',  InteriorEZHelp;
    Angle alpha /\ Angle (angle A O G)  /\ Angle gamma     [angles] by H0, AngleOrdering_DEF, H2', -, ANGLE;
    alpha <_ang angle A O G     by H0, H2', -, AngleTrichotomy2;
    consider F such that
    F IN int_angle A O G /\ alpha === angle A O F     [FintAOG] by angles, AOGncol, -, AngleOrderingUse;
    F IN int_angle A O B     by H2', -, InteriorTransitivity;
  qed     by angles, H2', -, FintAOG, AngleOrdering_DEF;
`;;

let AngleTrichotomy = thm `;
  let alpha beta be point_set;
  assume Angle alpha /\ Angle beta                              [H1];
  thus (alpha === beta  \/  alpha <_ang beta  \/  beta <_ang alpha)  /\
       ~(alpha === beta  /\  alpha <_ang beta)  /\
       ~(alpha === beta  /\  beta <_ang alpha)  /\
       ~(alpha <_ang beta  /\  beta <_ang alpha)

  proof
    ~(alpha === beta  /\  alpha <_ang beta)     [Not12] by AngleTrichotomy1;
    ~(alpha === beta  /\  beta <_ang alpha)     [Not13] by H1, C5Symmetric, AngleTrichotomy1;
    ~(alpha <_ang beta  /\  beta <_ang alpha)     [Not23] by H1, AngleOrderTransitivity, AngleTrichotomy1, C5Reflexive;
    consider P O A such that
    alpha = angle P O A /\ ~Collinear P O A     [POA] by H1, ANGLE;
    ~(P = O) /\ ~(O = A)      [Distinct] by -, NonCollinearImpliesDistinct;
    consider a such that
    Line a /\ O IN a /\ A IN a     [a_line] by -, I1;
    P NOTIN a     [notPa] by -, Distinct, I1, POA, Collinear_DEF, NOTIN;
    ?! r. Ray r /\ ? Q. ~(O = Q) /\ r = ray O Q /\ Q NOTIN a /\ Q,P same_side a /\ angle A O Q === beta     by H1, Distinct, a_line, -, C4;
    consider Q such that
    ~(O = Q) /\ Q NOTIN a /\ Q,P same_side a /\ angle A O Q === beta     [Qexists] by -;
    O NOTIN open (Q,P)     [notQOP] by a_line, Qexists, SameSide_DEF, NOTIN;
    ~Collinear A O P     [AOPncol] by POA, CollinearSymmetry;
    ~Collinear A O Q     [AOQncol] by a_line, Distinct, I1, Collinear_DEF, Qexists, NOTIN;
    Angle (angle A O P) /\ Angle (angle A O Q)     by AOPncol, -, ANGLE;
    alpha === angle A O P  /\  beta === angle A O Q  /\  angle A O P === alpha     [flip] by H1, -, POA, AngleSymmetry, C5Reflexive, Qexists, C5Symmetric;
    cases;
    suppose Collinear Q O P;
      Collinear O P Q by -, CollinearSymmetry;
      Q IN ray O P DELETE O     by Distinct, -, notQOP, IN_Ray, Qexists, IN_DELETE;
      ray O Q = ray O P     by Distinct, -, RayWellDefined;
      angle P O A = angle A O Q     by -, Angle_DEF, AngleSymmetry;
      alpha === beta     by -, POA, Qexists;
    qed     by -, Not12, Not13, Not23;
    suppose ~Collinear Q O P;
      P IN int_angle Q O A \/ Q IN int_angle P O A     by Distinct, a_line, Qexists, notPa, -, AngleOrdering;
      P IN int_angle A O Q \/ Q IN int_angle A O P     by -, InteriorAngleSymmetry;
      alpha <_ang angle A O Q  \/  beta <_ang angle A O P     by H1, AOQncol, AOPncol, -, flip, AngleOrdering_DEF;
      alpha <_ang beta  \/  beta <_ang alpha     by H1, -, Qexists, flip, AngleTrichotomy2;
    qed     by -, Not12, Not13, Not23;
  end;
`;;

let SupplementExists = thm `;
  let alpha be point_set;
  assume Angle alpha                [H1];
  thus ? alpha'. alpha suppl alpha'

  proof
    consider A O B such that
    alpha = angle A O B /\ ~Collinear A O B /\ ~(A = O)    [def_alpha] by H1, ANGLE, NonCollinearImpliesDistinct;
    consider A' such that
    O IN open (A,A')     by -, B2';
    angle A O B  suppl  angle A' O B     [AOBsup] by def_alpha, -, SupplementaryAngles_DEF, AngleSymmetry;
  qed     by -, def_alpha;
`;;

let SupplementImpliesAngle = thm `;
  let alpha beta be point_set;
  assume alpha suppl beta              [H1];
  thus Angle alpha /\ Angle beta

  proof
    consider A O B A' such that
    ~Collinear A O B  /\  O IN open (A,A')  /\  alpha = angle A O B  /\  beta = angle B O A'     [H1'] by H1, SupplementaryAngles_DEF;
    ~(O = A') /\ Collinear A O A'     [Distinct] by -, NonCollinearImpliesDistinct, B1';
    ~Collinear B O A'     by H1', CollinearSymmetry, -, NoncollinearityExtendsToLine;
  qed     by H1', -, ANGLE;
`;;

let RightImpliesAngle = thm `;
  ! alpha: point_set. Right alpha  ==>  Angle alpha
  by RightAngle_DEF, SupplementImpliesAngle;
`;;

let SupplementSymmetry = thm `;
  let alpha beta be point_set;
  assume alpha suppl beta [H1];
  thus beta suppl alpha

  proof
  consider A O B A' such that
  ~Collinear A O B  /\  O IN open (A,A')  /\  alpha = angle A O B  /\  beta = angle B O A'     [H1'] by H1, SupplementaryAngles_DEF;
  ~(O = A') /\ Collinear A O A'     by -, NonCollinearImpliesDistinct, B1';
  ~Collinear A' O B     [A'OBncol] by H1', CollinearSymmetry, -, NoncollinearityExtendsToLine;
  O IN open (A',A)  /\  beta = angle A' O B  /\  alpha = angle B O A by H1', B1',  AngleSymmetry;
  qed     by A'OBncol, -, SupplementaryAngles_DEF;
`;;

let SupplementsCongAnglesCong = thm `;
  let alpha beta alpha' beta' be point_set;
  assume alpha suppl alpha'  /\  beta suppl beta'      [H1];
  assume alpha === beta                  [H2];
  thus alpha' === beta'

  proof
    consider A O B A' such that
    ~Collinear A O B  /\  O IN open (A,A')  /\  alpha = angle A O B  /\  alpha' = angle B O A'     [def_alpha] by H1, SupplementaryAngles_DEF;
    ~(A = O) /\ ~(O = B) /\ ~(A = A') /\ ~(O = A') /\ Collinear A O A'     [Distinctalpha] by -, NonCollinearImpliesDistinct, B1';
    ~Collinear B A A' /\ ~Collinear O A' B     [BAA'ncol] by def_alpha, CollinearSymmetry, -, NoncollinearityExtendsToLine;
    Segment (seg O A) /\ Segment (seg O B) /\ Segment (seg O A')     [Osegments] by Distinctalpha, SEGMENT;
    consider C P D C' such that
    ~Collinear C P D  /\  P IN open (C,C')  /\  beta = angle C P D  /\  beta' = angle D P C'     [def_beta] by H1, SupplementaryAngles_DEF;
    ~(C = P) /\ ~(P = D) /\ ~(P = C')     [Distinctbeta] by def_beta, NonCollinearImpliesDistinct, B1';
    consider X such that
    X IN ray P C DELETE P  /\  seg P X === seg O A     [defX] by Osegments, Distinctbeta, C1;
    consider Y such that
    Y IN ray P D DELETE P  /\  seg P Y === seg O B  /\  ~(Y = P)     [defY] by Osegments, Distinctbeta, C1, IN_DELETE;
    consider X' such that
    X' IN ray P C' DELETE P  /\  seg P X' === seg O A'     [defX'] by Osegments, Distinctbeta, C1;
    P IN open (X',C)  /\  P IN open (X,X')       [XPX'] by def_beta, -, OppositeRaysIntersect1pointHelp, defX;
    ~(X = P) /\ ~(X' = P) /\ Collinear X P X' /\ ~(X = X') /\ ray A' O = ray A' A /\ ray X' P = ray X' X     [XPX'line] by defX, defX', IN_DELETE, -, B1', def_alpha, IntervalRay;
     Collinear P D Y /\ Collinear P C X     by defY, defX, IN_DELETE, IN_Ray;
    ~Collinear C P Y /\ ~Collinear X P Y     [XPYncol] by def_beta, -, defY, NoncollinearityExtendsToLine, CollinearSymmetry, XPX'line;
    ~Collinear Y X X' /\ ~Collinear P X' Y     [YXX'ncol] by -, CollinearSymmetry, XPX', XPX'line, NoncollinearityExtendsToLine;
    ray P X = ray P C  /\  ray P Y = ray P D  /\  ray P X' = ray P C'     [equalPrays] by Distinctbeta, defX, defY, defX', RayWellDefined;
    beta = angle X P Y  /\  beta' = angle Y P X'  /\  angle A O B === angle X P Y     [AOBeqXPY] by def_beta, -, Angle_DEF, H2, def_alpha;
   seg O A === seg P X  /\  seg O B === seg P Y  /\  seg A' O === seg X' P     [OAeq] by Osegments, XPX'line, SEGMENT, defX, defY, defX', C2Symmetric, SegmentSymmetry;
    seg A A' === seg X X'     [AA'eq] by def_alpha, XPX'line, XPX', -, SegmentSymmetry, C3;
    A,O,B cong X,P,Y     by def_alpha, XPYncol, OAeq, AOBeqXPY, SAS;
    seg A B === seg X Y  /\  angle B A O === angle Y X P     [AOBcong] by -, TriangleCong_DEF, AngleSymmetry;
    ray A O = ray A A'  /\  ray X P = ray X  X'  /\  angle B A A' === angle Y X X'     by def_alpha, XPX', IntervalRay, -, Angle_DEF;
    B,A,A' cong Y,X,X'     by BAA'ncol, YXX'ncol, AOBcong, -, AA'eq, -, SAS;
    seg A' B === seg X' Y  /\  angle A A' B === angle X X' Y     by -, TriangleCong_DEF, SegmentSymmetry;
    O,A',B cong P,X',Y     by BAA'ncol, YXX'ncol, OAeq, -, XPX'line, Angle_DEF, SAS;
    angle B O A' === angle Y P X'     by -, TriangleCong_DEF;
  qed     by -, equalPrays, def_beta, Angle_DEF, def_alpha;
`;;

let SupplementUnique = thm `;
  ! alpha beta beta': point_set. alpha suppl beta  /\   alpha suppl beta'  ==>  beta === beta'
  by SupplementaryAngles_DEF, ANGLE, C5Reflexive, SupplementsCongAnglesCong;
`;;

let CongRightImpliesRight = thm `;
  let alpha beta be point_set;
  assume Angle alpha  /\  Right beta            [H1];
  assume alpha === beta                          [H2];
  thus Right alpha

  proof
    consider alpha' beta' such that
    alpha suppl alpha'  /\  beta suppl beta'  /\  beta === beta'     [suppl] by H1, SupplementExists, H1, RightAngle_DEF;
    alpha' === beta'     [alpha'eqbeta'] by suppl, H2, SupplementsCongAnglesCong;
    Angle beta /\ Angle alpha' /\ Angle beta'     by suppl, SupplementImpliesAngle;
    alpha === alpha' by     H1, -, H2, suppl, alpha'eqbeta', C5Symmetric, C5Transitive;
  qed     by suppl, -, RightAngle_DEF;
`;;

let RightAnglesCongruentHelp = thm `;
  let A O B A' P be point;
  let a be point_set;
  assume ~Collinear A O B  /\  O IN open (A,A')                   [H1];
  assume Right (angle A O B)  /\  Right (angle A O P)                    [H2];
  thus P NOTIN int_angle A O B

  proof
    assume ~(P NOTIN int_angle A O B);
    P IN int_angle A O B     [PintAOB] by -, NOTIN;
    B IN int_angle P O A'  /\  B IN int_angle A' O P     [BintA'OP] by H1, -, InteriorReflectionInterior, InteriorAngleSymmetry ;
    ~Collinear A O P /\ ~Collinear P O A'     [AOPncol] by PintAOB, InteriorEZHelp, -, IN_InteriorAngle;
    angle A O B suppl angle B O A'  /\  angle A O P suppl angle P O A'     [AOBsup] by H1, -, SupplementaryAngles_DEF;
    consider alpha' beta' such that
    angle A O B suppl alpha'  /\  angle A O B === alpha'  /\  angle A O P suppl beta'  /\  angle A O P === beta'     [supplalpha'] by H2, RightAngle_DEF;
    alpha' === angle B O A'  /\  beta' === angle P O A'     [alpha'eqA'OB] by -, AOBsup, SupplementUnique;
    Angle (angle A O B) /\ Angle alpha' /\ Angle (angle B O A') /\ Angle (angle A O P) /\ Angle beta' /\ Angle (angle P O A')     [angles] by AOBsup, supplalpha', SupplementImpliesAngle, AngleSymmetry;
    angle A O B === angle B O A'  /\  angle A O P === angle P O A'     [H2'] by -, supplalpha', alpha'eqA'OB, C5Transitive;
    angle A O P === angle A O P  /\  angle B O A' === angle B O A'     [refl] by angles, C5Reflexive;
    angle A O P <_ang angle A O B  /\  angle B O A' <_ang angle P O A'     [BOA'lessPOA'] by angles, H1, PintAOB, -, AngleOrdering_DEF, AOPncol, CollinearSymmetry, BintA'OP, AngleSymmetry;
    angle A O P <_ang angle B O A'     by -, angles, H2', AngleTrichotomy2;
    angle A O P <_ang angle P O A'     by -, BOA'lessPOA', AngleOrderTransitivity;
  qed     by -, H2', AngleTrichotomy1;
`;;

let RightAnglesCongruent = thm `;
  let alpha beta be point_set;
  assume Right alpha /\ Right beta [H1];
   thus alpha === beta

  proof
    consider alpha' such that
    alpha suppl alpha'  /\  alpha === alpha'     by H1, RightAngle_DEF;
    consider A O B A' such that
    ~Collinear A O B  /\  O IN open (A,A')  /\  alpha = angle A O B  /\  alpha' = angle B O A'     [def_alpha] by -, SupplementaryAngles_DEF;
    ~(A = O) /\ ~(O = B)     [Distinct] by def_alpha, NonCollinearImpliesDistinct, B1';
    consider a such that
    Line a /\ O IN a /\ A IN a     [a_line] by Distinct, I1;
    B NOTIN a     [notBa] by -, def_alpha, Collinear_DEF, NOTIN;
    Angle beta     by H1, RightImpliesAngle;
    ?! r. Ray r /\ ? P. ~(O = P) /\ r = ray O P /\ P NOTIN a /\ P,B same_side a /\ angle A O P === beta     by -, Distinct, a_line, notBa, C4;
    consider P such that
    ~(O = P) /\ P NOTIN a /\ P,B same_side a /\ angle A O P === beta     [defP] by -;
    O NOTIN open (P,B)     [notPOB] by a_line, -, SameSide_DEF, NOTIN;
    ~Collinear A O P     [AOPncol] by a_line, Distinct, I1, defP, Collinear_DEF, NOTIN;
    Right (angle A O P)     [AOPright] by -, ANGLE, H1, defP, CongRightImpliesRight;
    P NOTIN int_angle A O B  /\  B NOTIN int_angle A O P     by def_alpha, H1, -, AOPncol, AOPright, RightAnglesCongruentHelp;
    Collinear P O B     by Distinct, a_line, defP, notBa, -, AngleOrdering, InteriorAngleSymmetry, NOTIN;
    P IN ray O B DELETE O     by Distinct, -, CollinearSymmetry, notPOB, IN_Ray, defP, IN_DELETE;
    ray O P = ray O B  /\  angle A O P = angle A O B     by Distinct, -, RayWellDefined, Angle_DEF;
  qed     by -, defP, def_alpha;
`;;

let OppositeRightAnglesLinear = thm `;
  let A B O H be point;
  let h be point_set;
  assume ~Collinear A O H /\ ~Collinear H O B                    [H0];
  assume Right (angle A O H) /\ Right (angle H O B)                      [H1];
  assume Line h /\ O IN h /\ H IN h  /\  ~(A,B same_side h)          [H2];
  thus O IN open (A,B)

  proof
    ~(A = O) /\ ~(O = H) /\ ~(O = B)     [Distinct] by  H0, NonCollinearImpliesDistinct;
    A NOTIN h /\ B NOTIN h     [notABh] by H0, H2, Collinear_DEF, NOTIN;
    consider E such that
    O IN open (A,E) /\ ~(E = O)     [AOE] by Distinct, B2', B1';
    angle A O H  suppl  angle H O E     [AOHsupplHOE] by H0, -, SupplementaryAngles_DEF;
    E NOTIN h     [notEh] by H2, NOTIN, AOE, BetweenLinear, notABh;
    ~(A,E same_side  h)     by H2, AOE, SameSide_DEF;
    B,E same_side  h     [Bsim_hE] by H2, notABh, notEh, -, H2, AtMost2Sides;
    consider alpha' such that
    angle A O H  suppl  alpha'  /\  angle A O H === alpha'     [AOHsupplalpha'] by H1, RightAngle_DEF;
    Angle (angle H O B) /\ Angle (angle A O H) /\ Angle alpha' /\ Angle (angle H O E)     [angalpha'] by H1, RightImpliesAngle, -, AOHsupplHOE, SupplementImpliesAngle;
    angle H O B === angle A O H  /\  alpha' === angle H O E     by H1, RightAnglesCongruent, AOHsupplalpha', AOHsupplHOE, SupplementUnique;
    angle H O B === angle H O E     by angalpha', -, AOHsupplalpha', C5Transitive;
    ray O B = ray O E     by H2, Distinct, notABh, notEh, Bsim_hE, -, C4Uniqueness;
    B IN ray O E DELETE O     by Distinct, EndpointInRay, -, IN_DELETE;
  qed     by AOE, -, OppositeRaysIntersect1pointHelp, B1';
`;;

let RightImpliesSupplRight = thm `;
  let A O B A' be point;
  assume ~Collinear A O B                       [H1];
  assume O IN open (A,A')                        [H2];
  assume Right (angle A O B)                        [H3];
  thus Right (angle B O A')

  proof
    angle A O B suppl angle B O A'  /\  Angle (angle A O B)  /\  Angle (angle B O A')     [AOBsuppl] by H1, H2, SupplementaryAngles_DEF, SupplementImpliesAngle;
    consider beta such that
    angle A O B suppl beta /\ angle A O B === beta     [betasuppl] by H3, RightAngle_DEF;
    Angle beta  /\  beta === angle A O B     [angbeta] by -, SupplementImpliesAngle, C5Symmetric;
    angle B O A' === beta     by AOBsuppl, betasuppl, SupplementUnique;
    angle B O A' === angle A O B     by AOBsuppl, angbeta, -, betasuppl, C5Transitive;
  qed     by AOBsuppl, H3, -, CongRightImpliesRight;
`;;

let IsoscelesCongBaseAngles = thm `;
  let A B C be point;
  assume ~Collinear A B C       [H1];
  assume seg B A === seg B C      [H2];
  thus  angle C A B  === angle A C B

  proof
    ~(A = B) /\ ~(B = C) /\ ~Collinear C B A     [CBAncol] by H1, NonCollinearImpliesDistinct, CollinearSymmetry;
    seg B C === seg B A  /\  angle A B C === angle C B A     by -, SEGMENT, H2, C2Symmetric, H1, ANGLE, AngleSymmetry, C5Reflexive;
    A,B,C cong C,B,A     by H1, CBAncol, H2, -, SAS;
  qed     by -, TriangleCong_DEF;
`;;

let C4withC1 = thm `;
  let alpha l be point_set;
  let O A Y P Q be point;
  assume Angle alpha /\ ~(O = A) /\ ~(P = Q)                  [H1];
  assume Line l /\ O IN l /\ A IN l /\ Y NOTIN l                [l_line];
  thus ? N. ~(O = N) /\ N NOTIN l /\ N,Y same_side l /\ seg O N === seg P Q /\ angle A O N === alpha

  proof
    ?! r. Ray r /\ ? B. ~(O = B) /\ r = ray O B /\ B NOTIN l /\ B,Y same_side l /\ angle A O B === alpha     by H1, l_line, C4;
    consider B such that
    ~(O = B) /\ B NOTIN l /\ B,Y same_side l /\ angle A O B === alpha     [Bexists] by -;
    consider N such that
    N IN ray O B DELETE O  /\  seg O N === seg P Q     [Nexists] by H1, -, SEGMENT, C1;
    ~(O = N)     [notON] by -, IN_DELETE;
    N NOTIN l /\ N,B same_side l     [notNl] by l_line, Bexists, Nexists, RaySameSide;
    N,Y same_side l     [Nsim_lY] by l_line, -, Bexists, SameSideTransitive;
    ray O N = ray O B  /\  angle A O N === alpha     by Bexists, Nexists, RayWellDefined, Angle_DEF;
  qed     by notON, notNl, Nsim_lY, Nexists, -;
`;;

let C4OppositeSide = thm `;
  let alpha l be point_set;
  let O A Z P Q be point;
  assume Angle alpha /\ ~(O = A) /\ ~(P = Q)                  [H1];
  assume Line l /\ O IN l /\ A IN l /\ Z NOTIN l                 [l_line];
  thus ? N. ~(O = N) /\ N NOTIN l /\ ~(Z,N same_side l) /\ seg O N === seg P Q /\ angle A O N === alpha

  proof
    ~(Z = O)     by l_line, NOTIN;
    consider Y such that
    O IN open (Z,Y)     [ZOY] by -, B2';
    ~(O = Y) /\ Collinear Z O Y     by -, B1';
    Y NOTIN l     [notYl] by l_line, I1, -, Collinear_DEF, NOTIN;
    consider N such that
    ~(O = N) /\ N NOTIN l  /\  N,Y same_side l  /\ seg O N === seg P Q  /\  angle A O N === alpha     [Nexists] by H1, l_line, notYl, C4withC1;
    ~(Z,Y same_side l)     by l_line, ZOY, SameSide_DEF;
    ~(Z,N same_side l)     by l_line, Nexists, notYl, -, SameSideTransitive;
  qed by -, Nexists;
`;;

let SSS = thm `;
  let A B C A' B' C' be point;
  assume ~Collinear A B C /\ ~Collinear A' B' C'                                 [H1];
  assume seg A B === seg A' B'  /\  seg A C === seg A' C'  /\  seg B C === seg B' C'            [H2];
  thus A,B,C cong A',B',C'

  proof
    ~(A = B) /\ ~(A = C) /\ ~(B = C) /\ ~(A' = B') /\ ~(B' = C')     [Distinct] by H1, NonCollinearImpliesDistinct;
    consider h such that
    Line h /\ A IN h /\ C IN h     [h_line] by Distinct, I1;
    B NOTIN h     [notBh] by h_line, H1, NOTIN, Collinear_DEF;
    Segment (seg A B) /\ Segment (seg C B) /\ Segment (seg A' B') /\ Segment (seg C' B')     [segments] by Distinct, -, SEGMENT;
    Angle (angle C' A' B')     by H1, CollinearSymmetry, ANGLE;
    consider N such that
    ~(A = N) /\ N NOTIN h /\ ~(B,N same_side h) /\ seg A N === seg A' B'  /\  angle C A N === angle C' A' B'     [Nexists] by -, Distinct, h_line, notBh, C4OppositeSide;
    ~(C = N)     by h_line, Nexists, NOTIN;
    Segment (seg A N) /\ Segment (seg C N)     [segN] by Nexists, -, SEGMENT;
    ~Collinear A N C     [ANCncol] by h_line, Distinct, I1, Collinear_DEF, Nexists, NOTIN;
    Angle (angle A B C) /\ Angle (angle A' B' C') /\ Angle (angle A N C)     [angles] by H1, -, ANGLE;
    seg A B === seg A N     [ABeqAN] by segments, segN, Nexists, H2, C2Symmetric, C2Transitive;
    C,A,N cong C',A',B'     by ANCncol, H1, CollinearSymmetry, H2, Nexists, SAS;
    angle A N C === angle A' B' C'  /\  seg C N === seg C' B'     [ANCeq] by -, TriangleCong_DEF;
    seg C B === seg C N     [CBeqCN] by segments, segN, -, H2, SegmentSymmetry, C2Symmetric, C2Transitive;
    consider G such that
    G IN h /\ G IN open (B,N)     [BGN] by Nexists, h_line, SameSide_DEF;
    ~(B = N)     [notBN] by -, B1';
    ray B G = ray B N  /\  ray N G = ray N B     [Grays] by BGN, B1', IntervalRay;
    consider v such that
    Line v /\ B IN v /\ N IN v     [v_line] by notBN, I1;
    G IN v /\ ~(h = v)     by v_line, BGN, BetweenLinear, notBh, NOTIN;
    h INTER v = {G}     [hvG] by h_line, v_line, -, BGN, I1Uniqueness;
    ~(G = A)  ==>  angle A B G === angle A N G [ABGeqANG]
    proof
      assume ~(G = A) [notGA];
      A NOTIN v     by hvG, h_line, -, EquivIntersectionHelp, IN_DELETE;
      ~Collinear B A N     by v_line, notBN, I1, Collinear_DEF, -, NOTIN;
      angle N B A === angle B N A     by -, ABeqAN, IsoscelesCongBaseAngles;
      angle G B A === angle G N A     by -, Grays, Angle_DEF, notGA;
    qed by -, AngleSymmetry;
    ~(G = C)  ==>  angle G B C === angle G N C [GBCeqGNC]
    proof
      assume ~(G = C) [notGC];
      C NOTIN v     by hvG, h_line, -, EquivIntersectionHelp, IN_DELETE;
      ~Collinear B C N     by v_line, notBN, I1, Collinear_DEF, -, NOTIN;
      angle N B C === angle B N C     by -, CBeqCN, IsoscelesCongBaseAngles, AngleSymmetry;
    qed     by -, Grays, Angle_DEF;
    angle A B C === angle A N C
    proof
      cases;
      suppose G = A     [GA];
        ~(G = C)     by -, Distinct;
      qed     by -, GBCeqGNC, GA;
      suppose G = C     [GC];
        ~(G = A)     by -, Distinct;
      qed     by -, ABGeqANG, GC;
      suppose ~(G = A) /\ ~(G = C)     [AGCdistinct];
        angle A B G === angle A N G  /\  angle G B C === angle G N C     [Gequivs] by -, ABGeqANG, GBCeqGNC;
        ~Collinear G B C /\ ~Collinear G N C /\ ~Collinear G B A /\ ~Collinear G N A     [Gncols] by h_line, BGN, AGCdistinct, I1, Collinear_DEF, notBh, Nexists, NOTIN;
        Collinear A G C     by h_line, BGN, Collinear_DEF;
        G IN open (A,C) \/ C IN open (G,A) \/ A IN open (C,G)     by Distinct, AGCdistinct, -, B3';
        cases by -;
        suppose G IN open (A,C);
          G IN int_angle A B C  /\  G IN int_angle A N C     by H1, ANCncol, -, ConverseCrossbar;
        qed     by -, Gequivs, AngleAddition;
        suppose C IN open (G,A);
          C IN int_angle G B A  /\  C IN int_angle G N A     by Gncols, -, B1', ConverseCrossbar;
        qed     by -, Gequivs, AngleSubtraction, AngleSymmetry;
        suppose A IN open (C,G);
          A IN int_angle G B C  /\  A IN int_angle G N C     by Gncols, -, B1', ConverseCrossbar;
        qed     by -, Gequivs, AngleSymmetry, AngleSubtraction;
      end;
    end;
    angle A B C === angle A' B' C'     by angles, -, ANCeq, C5Transitive;
  qed     by H1, H2, SegmentSymmetry, -, SAS;
`;;

let AngleBisector = thm `;
  let A B C be point;
  assume ~Collinear B A C                                       [H1];
  thus ? F. F IN int_angle B A C  /\  angle B A F === angle F A C

  proof
    ~(A = B) /\ ~(A = C)     [Distinct] by H1, NonCollinearImpliesDistinct;
    consider D such that
    B IN open (A,D)     [ABD] by Distinct, B2';
    ~(A = D) /\ Collinear A B D /\ Segment (seg A D)     [ABD'] by -, B1', SEGMENT;
    consider E such that
    E IN ray A C DELETE A  /\  seg A E === seg A D  /\  ~(A = E)     [ErAC] by -, Distinct, C1, IN_DELETE, IN_Ray;
    Collinear A C E  /\  D IN ray A B DELETE A     [notAE] by ErAC, IN_DELETE, IN_Ray, ABD, IntervalRayEZ;
    ray A D = ray A B  /\  ray A E =  ray A C     [equalrays] by Distinct, notAE, ErAC, RayWellDefined;
    ~Collinear D A E /\ ~Collinear E A D /\ ~Collinear A E D     [EADncol] by H1, ABD', notAE, ErAC, CollinearSymmetry, NoncollinearityExtendsToLine;
    angle D E A === angle E D A     [DEAeq] by EADncol, ErAC, IsoscelesCongBaseAngles;
    ~Collinear E D A /\ Angle (angle E D A) /\ ~Collinear A D E /\ ~Collinear D E A     [angEDA] by EADncol, CollinearSymmetry, ANGLE;
    ~(D = E)     [notDE] by EADncol, NonCollinearImpliesDistinct;
    consider h such that
    Line h /\ D IN h /\ E IN h     [h_line] by -, I1;
    A NOTIN h     [notAh] by -, Collinear_DEF, EADncol, NOTIN;
    consider F such that
    ~(D = F)  /\  F NOTIN h  /\  ~(A,F same_side h)  /\  seg D F === seg D A  /\  angle E D F === angle E D A     [Fexists] by angEDA, notDE, ABD', h_line, -, C4OppositeSide;
    ~(A = F)     [notAF] by h_line, -, SameSideReflexive;
    ~Collinear E D F /\ ~Collinear D E F /\ ~Collinear F E D     [EDFncol] by h_line, notDE, I1, Collinear_DEF, Fexists, NOTIN;
    seg D E === seg D E  /\  seg F A === seg F A     [FArefl] by notDE, notAF, SEGMENT, C2Reflexive;
    E,D,F cong E,D,A     by EDFncol, angEDA, -, Fexists, SAS;
    seg F E === seg A E /\ angle F E D === angle A E D     [FEDcong] by -, TriangleCong_DEF, SegmentSymmetry;
    angle E D A === angle D E A  /\  angle E D A === angle E D F  /\  angle D E A === angle D E F    [EDAeqEDF] by EDFncol, ANGLE, angEDA, Fexists, FEDcong, DEAeq, C5Symmetric, AngleSymmetry;
    consider G such that
    G IN h /\ G IN open (A,F)     [AGF] by Fexists, h_line, SameSide_DEF;
    F IN ray A G DELETE A     [FrAG] by -, IntervalRayEZ;
    consider v such that
    Line v /\ A IN v /\ F IN v /\ G IN v     [v_line] by notAF, I1, AGF, BetweenLinear;
    ~(v = h)  /\  v INTER h = {G}     [vhG] by -, notAh, NOTIN, h_line, AGF, I1Uniqueness;
    D NOTIN v     [notDv]
    proof
      assume ~(D NOTIN v);
      D IN v  /\  D = G     [DG] by h_line, -, NOTIN, vhG, IN_INTER, IN_SING;
      D IN open (A,F)     by DG, AGF;
      angle E D A suppl angle E D F     [EDAsuppl] by angEDA, -, SupplementaryAngles_DEF, AngleSymmetry;
      Right (angle E D A)     by EDAsuppl, EDAeqEDF, RightAngle_DEF;
      Right (angle A E D)     [RightAED] by angEDA, ANGLE, -, DEAeq, CongRightImpliesRight, AngleSymmetry;
      Right (angle D E F)     by EDFncol, ANGLE, -, FEDcong, CongRightImpliesRight, AngleSymmetry;
      E IN open (A,F)     by EADncol, EDFncol, RightAED, -, h_line, Fexists,  OppositeRightAnglesLinear;
      E IN v  /\  E = G     by v_line, -, BetweenLinear, h_line, vhG, IN_INTER, IN_SING;
    qed     by -, DG, notDE;
    E NOTIN v     [notEv]
    proof
      assume ~(E NOTIN v);
      E IN v  /\  E = G     [EG] by h_line, -, NOTIN, vhG, IN_INTER, IN_SING;
      E IN open (A,F)     by -, AGF;
      angle D E A suppl angle D E F     [DEAsuppl] by EADncol, -, SupplementaryAngles_DEF, AngleSymmetry;
      Right (angle D E A)     [RightDEA] by DEAsuppl, EDAeqEDF, RightAngle_DEF;
      Right (angle E D A)     [RightEDA] by angEDA, RightDEA, EDAeqEDF, CongRightImpliesRight;
      Right (angle E D F)     by EDFncol, ANGLE, RightEDA, Fexists, CongRightImpliesRight;
      D IN open (A,F)     by angEDA, EDFncol, RightEDA, AngleSymmetry, -, h_line, Fexists,  OppositeRightAnglesLinear;
      D IN v /\ D = G     by v_line, -, BetweenLinear, h_line, vhG, IN_INTER, IN_SING;
    qed     by -, EG, notDE;
    ~Collinear F A E /\ ~Collinear F A D  /\  ~(F = E)     [FAEncol] by v_line, notAF, I1, Collinear_DEF, notEv, notDv, NOTIN, NonCollinearImpliesDistinct;
    seg F E === seg A D     [FEeqAD] by -, ErAC, ABD', SEGMENT, FEDcong, ErAC, C2Transitive;
    seg A D === seg F D     by SegmentSymmetry, ABD', Fexists, SEGMENT, C2Symmetric;
    seg F E === seg F D     by FAEncol, ABD', Fexists, SEGMENT, FEeqAD, -, C2Transitive;
    F,A,E cong F,A,D     by FAEncol, FArefl, -, ErAC, SSS;
    angle F A E === angle F A D     [FAEeq] by -, TriangleCong_DEF;
    angle D A F === angle F A E     by FAEncol, ANGLE, FAEeq, C5Symmetric, AngleSymmetry;
    angle B A F === angle F A C     [BAFeqFAC] by -, equalrays, Angle_DEF;
    ~(E,D same_side v)
    proof
      assume E,D same_side v;
      ray A D = ray A E     by v_line, notAF, notDv, notEv, -, FAEeq, C4Uniqueness;
    qed by ABD', EndpointInRay, -, IN_Ray, EADncol;
    consider H such that
    H IN v /\ H IN open (E,D)     [EHD] by v_line, -, SameSide_DEF;
    H = G     by -, h_line, BetweenLinear, IN_INTER, vhG, IN_SING;
    G IN int_angle E A D     [GintEAD] by EADncol,  -, EHD, ConverseCrossbar;
    F IN int_angle E A D     [FintEAD] by GintEAD, FrAG, WholeRayInterior;
    B IN ray A D DELETE A   /\   C IN ray A E DELETE A     by equalrays, Distinct, EndpointInRay, IN_DELETE;
    F IN int_angle B A C     by FintEAD, -, InteriorWellDefined, InteriorAngleSymmetry;
  qed     by -, BAFeqFAC;
`;;

let EuclidPropositionI_6 = thm `;
  let A B C be point;
  assume ~Collinear A B C                       [H1];
  assume angle B A C === angle B C A                      [H2];
  thus seg B A === seg B C

  proof
    ~(A = C)     by H1, NonCollinearImpliesDistinct;
    seg C A === seg A C     [CAeqAC] by SegmentSymmetry, -, SEGMENT, C2Reflexive;
    ~Collinear B C A /\ ~Collinear C B A /\ ~Collinear B A C     [BCAncol] by H1, CollinearSymmetry;
    angle A C B === angle C A B     by -, ANGLE, H2, C5Symmetric, AngleSymmetry;
    C,B,A cong A,B,C     by H1, BCAncol, CAeqAC, H2, -, ASA;
  qed by -, TriangleCong_DEF;
`;;

let IsoscelesExists = thm `;
  let A B be point;
  assume ~(A = B)                                       [H1];
  thus ? D. ~Collinear A D B  /\  seg D A === seg D B

  proof
    consider l such that
    Line l /\ A IN l /\ B IN l     [l_line] by H1, I1;
    consider C such that
    C NOTIN l     [notCl] by -, ExistsPointOffLine;
    ~Collinear C A B /\ ~Collinear C B A /\ ~Collinear A B C /\ ~Collinear A C B /\ ~Collinear B A C     [CABncol] by l_line, H1, I1, Collinear_DEF, -, NOTIN;
    angle C A B === angle C B A  \/  angle C A B <_ang angle C B A  \/  angle C B A <_ang angle C A B     by -, ANGLE, AngleTrichotomy;
    cases by -;
    suppose angle C A B === angle C B A;
    qed     by -, CABncol, EuclidPropositionI_6;
    suppose angle C A B <_ang angle C B A;
      angle C A B <_ang angle A B C     by -, AngleSymmetry;
      consider E such that
      E IN int_angle A B C  /\  angle C A B === angle A B E     [Eexists] by CABncol, ANGLE, -, AngleOrderingUse;
      ~(B = E)     [notBE] by -, InteriorEZHelp;
      consider D such that
      D IN open (A,C)  /\  D IN ray B E DELETE B     [Dexists] by Eexists, Crossbar_THM;
      D IN int_angle A B C     by Eexists, -, WholeRayInterior;
      ~Collinear A D B     [ADBncol] by -, InteriorEZHelp, CollinearSymmetry;
      ray B D = ray B E  /\  ray A D = ray A C     by notBE, Dexists, RayWellDefined, IntervalRay;
      angle D A B === angle A B D     by Eexists, -, Angle_DEF;
    qed     by ADBncol, -, AngleSymmetry, EuclidPropositionI_6;
    :: similar case
    suppose angle C B A <_ang angle C A B;
      angle C B A <_ang angle B A C     by -, AngleSymmetry;
      consider E such that
      E IN int_angle B A C  /\  angle C B A === angle B A E     [Eexists] by CABncol, ANGLE, -, AngleOrderingUse;
      ~(A = E)     [notAE] by -, InteriorEZHelp;
      consider D such that
      D IN open (B,C) /\ D IN ray A E DELETE A     [Dexists] by Eexists, Crossbar_THM;
      D IN int_angle B A C     by Eexists, -, WholeRayInterior;
      ~Collinear A D B /\ ~Collinear D A B /\ ~Collinear D B A     [ADBncol] by -, InteriorEZHelp, CollinearSymmetry;
      ray A D = ray A E  /\  ray B D = ray B C     by notAE, Dexists, RayWellDefined, IntervalRay;
      angle D B A === angle B A D     by Eexists, -, Angle_DEF;
      angle D A B === angle D B A     by AngleSymmetry,  ADBncol, ANGLE, -, C5Symmetric;
    qed     by ADBncol, -, EuclidPropositionI_6;
  end;
`;;

let MidpointExists = thm `;
  let A B be point;
  assume ~(A = B)                                       [H1];
  thus ? M. M IN open (A,B)  /\  seg A M === seg M B

  proof
    consider D such that
    ~Collinear A D B  /\  seg D A === seg D B     [Dexists] by H1, IsoscelesExists;
    consider F such that
    F IN int_angle A D B  /\  angle A D F === angle F D B     [Fexists] by -, AngleBisector;
    ~(D = F)     [notDF] by -, InteriorEZHelp;
    consider M such that
    M IN open (A,B) /\  M IN ray D F DELETE D     [Mexists] by Fexists, Crossbar_THM;
    ray D M = ray D F     by notDF, -, RayWellDefined;
    angle A D M === angle M D B     [ADMeqMDB] by Fexists, -, Angle_DEF;
    M IN int_angle A D B     by Fexists, Mexists, WholeRayInterior;
    ~(D = M) /\ ~Collinear A D M /\ ~Collinear B D M     [ADMncol] by -, InteriorEZHelp, InteriorAngleSymmetry;
    seg D M === seg D M     by -, SEGMENT, C2Reflexive;
    A,D,M cong B,D,M     by ADMncol, Dexists, -, ADMeqMDB, AngleSymmetry, SAS;
  qed     by Mexists, -, TriangleCong_DEF, SegmentSymmetry;
`;;

let EuclidPropositionI_7short = thm `;
  let A B C D be point;
  let a be point_set;
  assume ~(A = B) /\ Line a /\ A IN a /\ B IN a                      [a_line];
  assume ~(C = D) /\ C NOTIN a /\ D NOTIN a /\ C,D same_side a             [Csim_aD];
  assume seg A C === seg A D                                      [ACeqAD];
  thus ~(seg B C === seg B D)

  proof
    ~(A = C) /\ ~(A = D)     [AnotCD] by a_line, Csim_aD, NOTIN;
    assume seg B C === seg B D;
    seg C B === seg D B  /\  seg A B === seg A B  /\  seg A D === seg A D     [segeqs] by -, SegmentSymmetry, a_line, AnotCD, SEGMENT, C2Reflexive;
    ~Collinear A C B  /\ ~Collinear A D B     by a_line, I1, Csim_aD, Collinear_DEF, NOTIN;
    A,C,B cong A,D,B     by -, ACeqAD, segeqs, SSS;
    angle B A C === angle B A D     by -, TriangleCong_DEF;
    ray A D = ray A C     by a_line, Csim_aD, -, C4Uniqueness;
    C IN ray A D DELETE A  /\  D IN ray A D DELETE A     by AnotCD, -, EndpointInRay, IN_DELETE;
    C = D     by AnotCD, SEGMENT, -, ACeqAD, segeqs, C1;
  qed     by -, Csim_aD;
`;;

let EuclidPropositionI_7Help = thm `;
  let A B C D be point;
  let a be point_set;
  assume ~(A = B)                                                       [notAB];
  assume Line a /\ A IN a /\ B IN a                                         [a_line];
  assume ~(C = D) /\ C NOTIN a /\ D NOTIN a /\ C,D same_side a                     [Csim_aD];
  assume seg A C === seg A D                                              [ACeqAD];
  assume C IN int_triangle D A B  \/  ConvexQuadrilateral A B C D         [Int_ConvQuad];
  thus ~(seg B C === seg B D)

  proof
    ~(A = C) /\ ~(A = D) /\ ~(B = C) /\ ~(B = D)     [Distinct] by a_line, Csim_aD, NOTIN, SameSide_DEF;
    cases by Int_ConvQuad;
    suppose ConvexQuadrilateral A B C D;
      A IN int_angle B C D  /\  B IN int_angle C D A  /\  Tetralateral A B C D    [ABint] by -, ConvexQuad_DEF, Quadrilateral_DEF;
      ~Collinear B C D /\ ~Collinear D C B /\ ~Collinear C B D /\ ~Collinear C D A /\ ~Collinear D A C /\ Angle (angle D C A) /\ Angle (angle C D B)     [angCDB] by -, Tetralateral_DEF, CollinearSymmetry, ANGLE;
      angle C D A === angle D C A     [CDAeqDCA] by angCDB, Distinct, SEGMENT, ACeqAD, C2Symmetric, IsoscelesCongBaseAngles;
      A IN int_angle D C B  /\  angle D C A === angle D C A  /\  angle C D B === angle C D B     by ABint, InteriorAngleSymmetry, angCDB, ANGLE, C5Reflexive;
      angle D C A <_ang angle D C B  /\  angle C D B <_ang angle C D A     by angCDB, ABint, -, AngleOrdering_DEF;
      angle C D B <_ang angle D C B     by -, angCDB, CDAeqDCA, AngleTrichotomy2, AngleOrderTransitivity;
      ~(angle D C B === angle C D B)     by -, AngleTrichotomy1, angCDB, ANGLE, C5Symmetric;
    qed     by angCDB, -, IsoscelesCongBaseAngles;
      suppose C IN int_triangle D A B;
      C IN int_angle A D B  /\  C IN int_angle D A B     [CintADB] by -, IN_InteriorTriangle, InteriorAngleSymmetry;
      ~Collinear A D C /\ ~Collinear B D C     [ADCncol] by CintADB, InteriorEZHelp, InteriorAngleSymmetry;
      ~Collinear D A C /\ ~Collinear C D A /\ ~Collinear A C D /\ ~Collinear A D C     [DACncol] by -, CollinearSymmetry;
      ~Collinear B C D /\ Angle (angle D C A) /\ Angle (angle C D B) /\ ~Collinear D C B     [angCDB] by ADCncol, -, CollinearSymmetry, ANGLE;
      angle C D A === angle D C A     [CDAeqDCA] by DACncol, Distinct, ADCncol, SEGMENT, ACeqAD, C2Symmetric, IsoscelesCongBaseAngles;
      consider E such that
      D IN open (A,E) /\ ~(D = E) /\ Collinear A D E     [ADE] by Distinct, B2', B1';
      B IN int_angle C D E /\ Collinear D A E     [BintCDE] by CintADB, -, InteriorReflectionInterior, CollinearSymmetry;
      ~Collinear C D E     [CDEncol] by DACncol, -, ADE, NoncollinearityExtendsToLine;
      consider F such that
      F IN open (B,D)  /\  F IN ray A C DELETE A     [Fexists] by CintADB, Crossbar_THM, B1';
      F IN int_angle B C D     [FintBCD] by ADCncol, CollinearSymmetry, -, ConverseCrossbar;
      ~Collinear D C F     [DCFncol] by Distinct, ADCncol, CollinearSymmetry, Fexists, B1', NoncollinearityExtendsToLine;
      Collinear A C F  /\  F IN ray D B DELETE D  /\  C IN int_angle A D F     by Fexists, IN_DELETE, IN_Ray, B1', IntervalRayEZ, CintADB, InteriorWellDefined;
      C IN open (A,F)     by -, AlternateConverseCrossbar;
      angle A D C suppl angle C D E  /\  angle A C D suppl angle D C F     by ADE, DACncol, -, SupplementaryAngles_DEF;
      angle C D E === angle D C F     [CDEeqDCF] by -, CDAeqDCA, AngleSymmetry, SupplementsCongAnglesCong;
      angle C D B <_ang angle C D E     by angCDB, CDEncol, BintCDE, C5Reflexive, AngleOrdering_DEF;
      angle C D B <_ang angle D C F     [CDBlessDCF] by -, DCFncol, ANGLE, CDEeqDCF, AngleTrichotomy2;
      angle D C F <_ang angle D C B     by DCFncol, ANGLE, angCDB, FintBCD, InteriorAngleSymmetry, C5Reflexive, AngleOrdering_DEF;
      angle C D B <_ang angle D C B     by CDBlessDCF, -, AngleOrderTransitivity;
      ~(angle D C B === angle C D B)     by -, AngleTrichotomy1, angCDB, CollinearSymmetry, ANGLE, C5Symmetric;
    qed     by Distinct, ADCncol, CollinearSymmetry, -, IsoscelesCongBaseAngles;
  end;
`;;

let EuclidPropositionI_7 = thm `;
  let A B C D be point;
  let a be point_set;
  assume ~(A = B)                                               [notAB];
  assume Line a /\ A IN a /\ B IN a                                 [a_line];
  assume ~(C = D) /\ C NOTIN a /\ D NOTIN a /\ C,D same_side a             [Csim_aD];
  assume seg A C === seg A D                                      [ACeqAD];
  thus ~(seg B C === seg B D)

  proof
    ~Collinear A B C /\ ~Collinear D A B     [ABCncol] by a_line, notAB, I1, Collinear_DEF, Csim_aD, NOTIN;
    ~(A = C) /\ ~(A = D) /\ ~(B = C) /\ ~(B = D) /\ A NOTIN open (C,D)     [Distinct] by a_line, Csim_aD, NOTIN, SameSide_DEF;
    ~Collinear A D C      [ADCncol]
    proof
      assume Collinear A D C;
      C IN ray A D DELETE A  /\  D IN ray A D DELETE A     by Distinct, -, IN_Ray, EndpointInRay, IN_DELETE;
    qed     by Distinct, SEGMENT, -, ACeqAD, C2Reflexive, C1, Csim_aD;
    D,C same_side a     [Dsim_aC] by a_line, Csim_aD, SameSideSymmetric;
    seg A D === seg A C  /\  seg B D === seg B D     [ADeqAC] by Distinct, SEGMENT, ACeqAD, C2Symmetric, C2Reflexive;
    ~Collinear D A C /\ ~Collinear C D A /\ ~Collinear A C D /\ ~Collinear A D C     [DACncol] by ADCncol, CollinearSymmetry;
    ~(seg B D === seg B C)  ==>  ~(seg B C === seg B D)     [BswitchDC] by Distinct, SEGMENT, C2Symmetric;
    cases;
    suppose Collinear B D C;
      B NOTIN open (C,D)  /\  C IN ray B D DELETE B  /\  D IN ray B D DELETE B     by a_line, Csim_aD, SameSide_DEF, NOTIN, Distinct, -, IN_Ray, Distinct, IN_DELETE, EndpointInRay;
    qed     by Distinct, SEGMENT, -, ACeqAD, ADeqAC, C1, Csim_aD;
    suppose ~Collinear B D C     [BDCncol];
      Tetralateral A B C D     by notAB, Distinct, Csim_aD, ABCncol, -, CollinearSymmetry, DACncol, Tetralateral_DEF;
      ConvexQuadrilateral A B C D  \/  C IN int_triangle D A B  \/
      ConvexQuadrilateral A B D C  \/  D IN int_triangle C A B     by -, a_line, Csim_aD,  FourChoicesTetralateral, InteriorTriangleSymmetry;
    qed     by notAB, a_line, Csim_aD, Dsim_aC, ACeqAD, ADeqAC, -, EuclidPropositionI_7Help, BswitchDC;
  end;
`;;

let EuclidPropositionI_11 = thm `;
  let A B be point;
  assume ~(A = B)                       [notAB];
  thus ? F. Right (angle A B F)

  proof
    consider C such that
    B IN open (A,C)  /\  seg B C === seg B A     [ABC] by notAB, SEGMENT, C1OppositeRay;
    ~(A = B) /\ ~(A = C) /\ ~(B = C) /\ Collinear A B C     [Distinct] by ABC, B1';
    seg B A === seg B C     [BAeqBC] by -, SEGMENT, ABC, C2Symmetric;
    consider F such that
    ~Collinear A F C  /\  seg F A  === seg F C     [Fexists] by Distinct, IsoscelesExists;
    ~Collinear B F A /\ ~Collinear B F C     [BFAncol] by -, CollinearSymmetry, Distinct, NoncollinearityExtendsToLine;
    ~Collinear A B F /\ Angle (angle A B F)     [angABF] by BFAncol, CollinearSymmetry, ANGLE;
    angle A B F suppl angle F B C     [ABFsuppl] by -, ABC, SupplementaryAngles_DEF;
    ~(B = F)  /\  seg B F === seg B F     by BFAncol, NonCollinearImpliesDistinct, SEGMENT, C2Reflexive;
    B,F,A cong B,F,C     by BFAncol, -, BAeqBC, Fexists, SSS;
    angle A B F === angle F B C     by -, TriangleCong_DEF, AngleSymmetry;
  qed     by angABF, ABFsuppl, -, RightAngle_DEF;
`;;

let DropPerpendicularToLine = thm `;
  let P be point;
  let l be point_set;
  assume Line l  /\  P NOTIN l                       [l_line];
  thus ? E Q. E IN l /\ Q IN l /\ Right (angle P Q E)

  proof
    consider A B such that
    A IN l /\ B IN l /\ ~(A = B)     [ABl] by l_line, I2;
    ~Collinear B A P /\ ~Collinear P A B /\ ~(A = P)     [BAPncol] by l_line, ABl, I1, Collinear_DEF, NOTIN, CollinearSymmetry, ABl, NOTIN;
    Angle (angle B A P) /\ Angle (angle P A B)     [angBAP] by -, ANGLE, AngleSymmetry;
    consider P' such that
    ~(A = P') /\ P' NOTIN l /\ ~(P,P' same_side l) /\ seg A P' === seg A P  /\  angle B A P' === angle B A P     [P'exists] by angBAP, ABl, BAPncol, l_line, C4OppositeSide;
    consider Q such that
    Q IN l /\ Q IN open (P,P') /\ Collinear A B Q     [Qexists] by l_line, -, SameSide_DEF, ABl, Collinear_DEF;
    ~Collinear B A P'     [BAP'ncol] by l_line, ABl, I1, Collinear_DEF, P'exists, NOTIN;
    angle B A P === angle B A P'     [BAPeqBAP'] by -, ANGLE, angBAP, P'exists, C5Symmetric;
    ? E. E IN l  /\  ~Collinear P Q E  /\  angle P Q E === angle E Q P'
    proof
      cases;
      suppose A = Q [AQ];
     qed     by ABl, AQ, BAPncol, BAPeqBAP', AngleSymmetry;
      suppose ~(A = Q)     [notAQ];
        seg A Q  === seg A Q  /\  seg A P === seg A P'     [APeqAP'] by -, SEGMENT, C2Reflexive, BAPncol, P'exists, C2Symmetric;
        ~Collinear Q A P' /\ ~Collinear Q A P     [QAP'ncol] by l_line, ABl, Qexists, notAQ, I1, Collinear_DEF, P'exists, NOTIN;
        angle Q A P === angle Q A P'
        proof
          cases;
          suppose A IN open (Q,B);
            angle B A P suppl angle P A Q   /\  angle B A P' suppl angle P' A Q     by BAPncol, BAP'ncol, -, B1',  SupplementaryAngles_DEF;
          qed     by -, BAPeqBAP', SupplementsCongAnglesCong, AngleSymmetry;
          suppose ~(A IN open (Q,B));
            A NOTIN open (Q,B)  /\  Q IN ray A B DELETE A  /\  ray A Q = ray A B     by -, NOTIN, ABl, Qexists, IN_Ray, notAQ, IN_DELETE, ABl, RayWellDefined;
          qed     by -, BAPeqBAP', Angle_DEF;
        end;
        Q,A,P cong Q,A,P'     by QAP'ncol, APeqAP', -, SAS;
      qed     by -, TriangleCong_DEF, AngleSymmetry, ABl, QAP'ncol, CollinearSymmetry;
    end;
    consider E such that
    E IN l /\ ~Collinear P Q E /\ angle P Q E === angle E Q P'     [Eexists] by -;
    angle P Q E suppl angle E Q P'  /\  Right (angle P Q E)     by -, Qexists, SupplementaryAngles_DEF, RightAngle_DEF;
  qed     by Eexists, Qexists, -;
`;;

let EuclidPropositionI_14 = thm `;
  let A B C D be point;
  let l be point_set;
  assume Line l /\ A IN l /\ B IN l /\ ~(A = B)              [l_line];
  assume C NOTIN l /\ D NOTIN l /\ ~(C,D same_side l)             [Cnsim_lD];
  assume angle C B A suppl angle A B D                  [CBAsupplABD];
  thus B IN open (C,D)

  proof
    ~(B = C) /\ ~(B = D) /\ ~Collinear C B A     [Distinct] by l_line, Cnsim_lD, NOTIN, I1, Collinear_DEF;
    consider E such that
    B IN open (C,E)     [CBE] by Distinct, B2';
    E NOTIN l /\ ~(C,E same_side l)     [Csim_lE] by l_line, NOTIN, -, BetweenLinear, Cnsim_lD, SameSide_DEF;
    D,E same_side l     [Dsim_lE] by l_line, Cnsim_lD, -, AtMost2Sides;
    angle C B A suppl angle A B E     by Distinct, CBE, SupplementaryAngles_DEF;
    angle A B D === angle A B E     by CBAsupplABD, -, SupplementUnique;
    ray B E = ray B D     by l_line, Csim_lE, Cnsim_lD, Dsim_lE, -, C4Uniqueness;
    D IN ray B E DELETE B     by Distinct, -, EndpointInRay, IN_DELETE;
  qed     by CBE, -, OppositeRaysIntersect1pointHelp, B1';
`;;

let VerticalAnglesCong = thm `;     :: Euclid's Proposition I.15
  let A B O A' B' be point;
  assume ~Collinear A O B                               [H1];
  assume O IN open (A,A')  /\  O IN open (B,B')            [H2];
  thus angle B O A' === angle B' O A

  proof
    angle A O B suppl angle B O A'     [AOBsupplBOA'] by H1, H2, SupplementaryAngles_DEF;
    angle B O A suppl angle A O B'     by H1, CollinearSymmetry, H2, SupplementaryAngles_DEF;
  qed     by AOBsupplBOA', -, AngleSymmetry, SupplementUnique;
`;;

let EuclidPropositionI_16 = thm `;
  let A B C D be point;
  assume ~Collinear A B C                               [H1];
  assume C IN open (B,D)                                 [H2];
  thus angle B A C <_ang angle D C A

  proof
    ~(A = B) /\ ~(A = C) /\ ~(B = C)     [Distinct] by H1, NonCollinearImpliesDistinct;
    consider l such that
    Line l /\ A IN l /\ C IN l     [l_line] by Distinct, I1;
    consider m such that
    Line m /\ B IN m /\ C IN m     [m_line] by Distinct, I1;
    D IN m     [Dm] by m_line, H2, BetweenLinear;
    consider E such that
    E IN open (A,C) /\ seg A E === seg E C     [AEC] by Distinct, MidpointExists;
    ~(A = E) /\ ~(E = C) /\ Collinear A E C /\ ~(B = E)     [AECcol] by -, B1', H1;
    E IN l     [El] by l_line, AEC, BetweenLinear;
    consider F such that
    E IN open (B,F) /\ seg E F === seg E B     [BEF] by AECcol, SEGMENT, C1OppositeRay;
    ~(B = E) /\ ~(B = F) /\ ~(E = F) /\ Collinear B E F     [BEF'] by BEF, B1';
    B NOTIN l     [notBl] by l_line, Distinct, I1, Collinear_DEF, H1, NOTIN;
    ~Collinear A E B /\ ~Collinear C E B     [AEBncol] by l_line, El, AECcol, I1, Collinear_DEF, notBl, NOTIN;
    Angle (angle B A E)     [angBAE] by -, CollinearSymmetry, ANGLE;
    ~Collinear C E F     [CEFncol] by AEBncol, BEF', CollinearSymmetry, NoncollinearityExtendsToLine;
    angle B E A === angle F E C     [BEAeqFEC] by AEBncol, AEC, B1', BEF, VerticalAnglesCong;
    seg E A === seg E C  /\  seg E B === seg E F     by AEC, SegmentSymmetry, AECcol, BEF',  SEGMENT, BEF, C2Symmetric;
    A,E,B cong C,E,F     by AEBncol, CEFncol, -, BEAeqFEC, AngleSymmetry, SAS;
    angle B A E === angle F C E     [BAEeqFCE] by -, TriangleCong_DEF;
    ~Collinear E C D     [ECDncol] by AEBncol, H2, B1', CollinearSymmetry, NoncollinearityExtendsToLine;
    F NOTIN l /\ D NOTIN l     [notFl] by l_line, El, Collinear_DEF, CEFncol, -, NOTIN;
    F IN ray B E DELETE B  /\  E NOTIN m     by BEF, IntervalRayEZ, m_line, Collinear_DEF, AEBncol, NOTIN;
    F NOTIN m  /\  F,E same_side m     [Fsim_mE] by m_line, -, RaySameSide;
    ~(B,F same_side l)  /\  ~(B,D same_side l)     by El, l_line, BEF, H2, SameSide_DEF;
    F,D same_side l     by l_line, notBl, notFl, -, AtMost2Sides;
    F IN int_angle E C D     by ECDncol, l_line, El, m_line, Dm, notFl, Fsim_mE, -, IN_InteriorAngle;
    angle B A E <_ang angle E C D     [BAElessECD] by angBAE, ECDncol, -, BAEeqFCE, AngleSymmetry, AngleOrdering_DEF;
    ray A E = ray A C  /\  ray C E = ray C A     by AEC, B1', IntervalRay;
    angle B A C <_ang angle A C D     by BAElessECD, -, Angle_DEF;
  qed     by -, AngleSymmetry;
`;;

let ExteriorAngle = thm `;
  let A B C D be point;
  assume ~Collinear A B C                               [H1];
  assume C IN open (B,D)                                 [H2];
  thus angle A B C <_ang angle A C D

  proof
    ~(C = D) /\ C IN open (D,B) /\ Collinear B C D     [H2'] by H2, BetweenLinear, B1';
    ~Collinear B A C /\ ~(A = C)     [BACncol] by H1, CollinearSymmetry, NonCollinearImpliesDistinct;
    consider E such that
    C IN open (A,E)     [ACE] by -, B2';
    ~(C = E) /\ C IN open (E,A) /\ Collinear A C E     [ACE'] by -, B1';
    ~Collinear A C D /\ ~Collinear D C E     [DCEncol] by H1, CollinearSymmetry, H2', -, NoncollinearityExtendsToLine;
    angle A B C <_ang angle E C B     [ABClessECB] by BACncol, ACE, EuclidPropositionI_16;
    angle E C B === angle A C D     by DCEncol, ACE', H2', VerticalAnglesCong;
  qed     by ABClessECB, DCEncol, ANGLE, -, AngleTrichotomy2;
`;;

let EuclidPropositionI_17 = thm `;
  let A B C be point;
  let alpha beta gamma be point_set;
  assume ~Collinear A B C  /\  alpha = angle A B C  /\  beta = angle B C A               [H1];
  assume beta suppl gamma                                                      [H2];
  thus alpha <_ang gamma

  proof
    Angle gamma [anggamma] by H2, SupplementImpliesAngle;
    ~(A = B) /\ ~(A = C) /\ ~(B = C)     [Distinct] by H1, NonCollinearImpliesDistinct;
    ~Collinear B A C /\ ~Collinear A C B     [BACncol] by H1, CollinearSymmetry;
    consider D such that
    C IN open (A,D)     [ACD] by Distinct, B2';
    angle A B C <_ang angle D C B     [ABClessDCB] by BACncol, ACD, EuclidPropositionI_16;
    beta suppl angle B C D     by -, H1, AngleSymmetry, BACncol, ACD, SupplementaryAngles_DEF;
    angle B C D === gamma     by H2, -, SupplementUnique;
  qed     by ABClessDCB, H1, AngleSymmetry, anggamma, -, AngleTrichotomy2;
`;;

let EuclidPropositionI_18 = thm `;
  let A B C be point;
  assume ~Collinear A B C                       [H1];
  assume seg A C <__ seg A B                    [H2];
  thus angle A B C <_ang angle B C A

  proof
    ~(A = B) /\ ~(A = C)     [Distinct] by H1, NonCollinearImpliesDistinct;
    consider D such that
    D IN open (A,B) /\ seg A C === seg A D     [ADB] by Distinct, SEGMENT, H2, SegmentOrderingUse;
    ~(D = A) /\ ~(D = B) /\ D IN open (B,A) /\ Collinear A D B /\ ray B D = ray B A     [ADB'] by -, B1', IntervalRay;
    D IN int_angle A C B     [DintACB] by H1, CollinearSymmetry, ADB, ConverseCrossbar;
    ~Collinear D A C /\ ~Collinear C B D     [DACncol] by H1, CollinearSymmetry, ADB', NoncollinearityExtendsToLine;
    seg A D === seg A C     by ADB', Distinct, SEGMENT, ADB, C2Symmetric;
    angle C D A === angle A C D     by DACncol, -, IsoscelesCongBaseAngles, AngleSymmetry;
    angle C D A <_ang angle A C B     [CDAlessACB] by DACncol, CollinearSymmetry, ANGLE, H1, CollinearSymmetry, DintACB, -, AngleOrdering_DEF;
    angle B D C suppl angle C D A     by DACncol, CollinearSymmetry, ADB', SupplementaryAngles_DEF;
    angle C B D <_ang angle C D A     by DACncol, -, EuclidPropositionI_17;
    angle C B D <_ang angle A C B     by -, CDAlessACB, AngleOrderTransitivity;
  qed     by -, ADB', Angle_DEF, AngleSymmetry;
`;;

let EuclidPropositionI_19 = thm `;
  let A B C be point;
  assume ~Collinear A B C                       [H1];
  assume angle A B C <_ang angle B C A                 [H2];
  thus seg A C  <__ seg A B

  proof
    ~Collinear B A C /\ ~Collinear B C A /\ ~Collinear A C B     [BACncol] by H1, CollinearSymmetry;
    ~(A = B) /\ ~(A = C)     [Distinct] by H1, NonCollinearImpliesDistinct;
    assume ~(seg A C  <__ seg A B);
    seg A B === seg A C   \/  seg A B  <__ seg A C     by Distinct, SEGMENT, -, SegmentTrichotomy;
    cases by -;
    suppose seg A B === seg A C;
      angle C B A === angle B C A     by BACncol, -, IsoscelesCongBaseAngles;
    qed     by -, AngleSymmetry, H2, AngleTrichotomy1;
    suppose seg A B  <__ seg A C;
      angle A C B <_ang angle C B A     by BACncol, -, EuclidPropositionI_18;
    qed     by H1, BACncol, ANGLE, -, AngleSymmetry, H2, AngleTrichotomy;
  end;
`;;

let EuclidPropositionI_20 = thm `;
  let A B C D be point;
  assume ~Collinear A B C                               [H1];
  assume A IN open (B,D)  /\  seg A D === seg A C           [H2];
  thus seg B C <__ seg B D

  proof
    ~(B = D) /\ ~(A = D) /\ A IN open (D,B) /\ Collinear B A D /\ ray D A = ray D B     [BAD'] by H2, B1', IntervalRay;
    ~Collinear C A D     [CADncol] by H1, CollinearSymmetry, BAD', NoncollinearityExtendsToLine;
    ~Collinear D C B /\ ~Collinear B D C     [DCBncol] by H1, CollinearSymmetry, BAD', NoncollinearityExtendsToLine; ::  13
    Angle (angle C D A)     [angCDA] by CADncol, CollinearSymmetry, ANGLE;
    angle C D A === angle D C A     [CDAeqDCA] by CADncol, CollinearSymmetry, H2, IsoscelesCongBaseAngles;
    A IN int_angle D C B     by DCBncol, BAD', ConverseCrossbar;
    angle C D A <_ang angle D C B     by angCDA, DCBncol, -, CDAeqDCA, AngleOrdering_DEF;
    angle B D C <_ang angle D C B     by -, BAD', Angle_DEF, AngleSymmetry;
  qed     by DCBncol, -, EuclidPropositionI_19;
`;;

let EuclidPropositionI_21 = thm `;
  let A B C D be point;
  assume ~Collinear A B C                       [H1];
  assume D IN int_triangle A B C                 [H2];
  thus angle A B C <_ang angle C D A

  proof
    ~(B = A) /\ ~(B = C) /\ ~(A = C)     [Distinct] by H1, NonCollinearImpliesDistinct;
    D IN int_angle B A C  /\  D IN int_angle C B A     [DintTri] by H2, IN_InteriorTriangle, InteriorAngleSymmetry;
    consider E such that
    E IN open (B,C) /\ E IN ray A D DELETE A     [BEC] by -, Crossbar_THM;
    ~(B = E) /\ ~(E = C) /\ Collinear B E C  /\  Collinear A D E      [BEC'] by -, B1', IN_DELETE, IN_Ray;
    ray B E = ray B C  /\  E IN ray B C DELETE B     [rBErBC] by BEC, IntervalRay, IntervalRayEZ;
    D IN int_angle A B E     [DintABE] by DintTri, -, InteriorAngleSymmetry, InteriorWellDefined;
    D IN open (A,E)     [ADE] by BEC', -, AlternateConverseCrossbar;
    ray E D = ray E A     [rEDrEA] by -, B1', IntervalRay;
    ~Collinear A B E /\ ~Collinear B E A  /\ ~Collinear C B D /\ ~(A = D)     [ABEncol] by DintABE, IN_InteriorAngle, CollinearSymmetry, DintTri, InteriorEZHelp;
    ~Collinear E D C /\ ~Collinear C E D     [EDCncol] by -, CollinearSymmetry, BEC',  NoncollinearityExtendsToLine;
    angle A B E <_ang angle A E C     by ABEncol, BEC, ExteriorAngle;
    angle A B C <_ang angle C E D     [ABClessAEC] by -, rBErBC, rEDrEA, Angle_DEF, AngleSymmetry;
    angle C E D  <_ang  angle C D A     by EDCncol, ADE, B1', ExteriorAngle;
  qed     by ABClessAEC, -, AngleOrderTransitivity;
`;;

let AngleTrichotomy3 = thm `;
  let alpha beta gamma be point_set;
  assume alpha <_ang beta  /\  Angle gamma  /\  gamma === alpha                  [H1];
  thus gamma <_ang beta

  proof
    consider A O B G such that
    Angle alpha /\ ~Collinear A O B /\ beta = angle A O B /\ G IN int_angle A O B /\ alpha === angle A O G     [H1'] by H1, AngleOrdering_DEF;
    ~Collinear A O G     by -, InteriorEZHelp;
    gamma === angle A O G     by H1, H1', -, ANGLE, C5Transitive;
  qed     by H1, H1', -, AngleOrdering_DEF;
`;;

let InteriorCircleConvexHelp = thm `;
  let O A B C be point;
  assume ~Collinear A O C                               [H1];
  assume B IN open (A,C)                                 [H2];
  assume seg O A <__ seg O C  \/  seg O A === seg O C      [H3];
  thus seg O B <__ seg O C

  proof
    ~Collinear O C A /\ ~Collinear C O A /\ ~(O = A) /\ ~(O = C)     [H1'] by H1, CollinearSymmetry, NonCollinearImpliesDistinct;
    ray A B = ray A C  /\  ray C B = ray C A     [equal_rays] by H2, IntervalRay, B1';
    angle O C A <_ang angle C A O  \/  angle O C A === angle C A O
    proof
      cases by H3;
      suppose seg O A <__ seg O C;
      qed     by H1', -, EuclidPropositionI_18;
      suppose seg O A === seg O C [seg_eq];
        seg O C === seg O A     by H1', SEGMENT, -, C2Symmetric;
      qed     by H1', -, IsoscelesCongBaseAngles, AngleSymmetry;
    end;
    angle O C B <_ang angle B A O  \/  angle O C B === angle B A O     by -, equal_rays, Angle_DEF;
    angle B C O <_ang angle O A B  \/  angle B C O === angle O A B     [BCOlessOAB] by -, AngleSymmetry;
    ~Collinear O A B /\ ~Collinear B C O /\ ~Collinear O C B     [OABncol] by H1, CollinearSymmetry, H2, B1', NoncollinearityExtendsToLine;
    angle O A B <_ang angle O B C     by -, H2, ExteriorAngle;
    angle B C O <_ang angle O B C by BCOlessOAB, -, AngleOrderTransitivity, OABncol, ANGLE, -, AngleTrichotomy3;
  qed     by OABncol, -, AngleSymmetry, EuclidPropositionI_19;
`;;

let InteriorCircleConvex = thm `;
  let O R A B C be point;
  assume  ~(O = R)                                      [H1];
  assume B IN open (A,C)                                 [H2];
  assume A IN int_circle O R  /\  C IN int_circle O R      [H3];
  thus B IN int_circle O R

  proof
    ~(A = B) /\ ~(A = C) /\ ~(B = C) /\ B IN open (C,A)     [H2'] by H2, B1';
    (A = O  \/  seg O A <__ seg O R)  /\  (C = O  \/  seg O C <__ seg O R)     [ACintOR] by H3, H1, IN_InteriorCircle;
    cases;
    suppose O = A \/ O = C;
      B IN open (O,C)  \/  B IN open (O,A)     by -, H2, B1';
      seg O B <__ seg O A /\ ~(O = A)  \/  seg O B <__ seg O C /\ ~(O = C)     by -, B1', SEGMENT, C2Reflexive,  SegmentOrdering_DEF;
      seg O B <__ seg O R     by -, ACintOR, SegmentOrderTransitivity;
    qed by -, H1, IN_InteriorCircle;
    suppose ~(O = A) /\ ~(O = C)     [OnotAC];
      cases;
      suppose ~Collinear A O C     [AOCncol];
        seg O A <__ seg O C  \/  seg O A === seg O C  \/  seg O C <__ seg O A     by OnotAC, SEGMENT,  SegmentTrichotomy;
        seg O B <__ seg O C  \/  seg O B <__ seg O A     by AOCncol, H2, -, InteriorCircleConvexHelp, CollinearSymmetry, B1';
      qed     by OnotAC, ACintOR, -, SegmentOrderTransitivity, H1, IN_InteriorCircle;
      suppose Collinear A O C                           [AOCcol];
        consider l such that
        Line l /\ A IN l /\ C IN l     by H2', I1;
        Collinear B A O /\ Collinear B C O     [OABCcol] by -, H2, BetweenLinear, H2', AOCcol, CollinearLinear, Collinear_DEF;
        B NOTIN open (O,A) /\ B NOTIN open (O,C)  ==>  B = O
        proof
          assume B NOTIN open (O,A) /\ B NOTIN open (O,C);
          O IN ray B A INTER ray B C     by H2', OABCcol, -, IN_Ray, IN_INTER;
        qed     by -, H2, OppositeRaysIntersect1point, IN_SING;
        B IN open (O,A)  \/  B IN open (O,C)  \/  B = O     by -, NOTIN;
        seg O B <__ seg O A  \/  seg O B <__ seg O C  \/  B = O     by -, B1', SEGMENT, C2Reflexive,  SegmentOrdering_DEF;
        seg O B <__ seg O R  \/  B = O     by -, ACintOR, OnotAC, SegmentOrderTransitivity;
      qed     by -, H1, IN_InteriorCircle;
    end;
  end;
`;;

let SegmentTrichotomy3 = thm `;
  let s t u be point_set;
  assume s <__ t  /\  Segment u  /\  u === s                [H1];
  thus u <__ t

  proof
    consider C D X such that
    Segment s /\ t = seg C D /\ X IN open (C,D) /\ s === seg C X /\ ~(C = X)     [H1'] by H1, SegmentOrdering_DEF, B1';
    u === seg C X     by H1, -, SEGMENT, C2Transitive;
  qed     by H1, H1', -, SegmentOrdering_DEF;
`;;

let EuclidPropositionI_24Help = thm `;
  let O A C O' D F be point;
  assume ~Collinear A O C /\ ~Collinear D O' F                   [H1];
  assume seg O' D === seg O A  /\  seg O' F === seg O C              [H2];
  assume  angle D O' F <_ang angle A O C                                [H3];
  assume seg O A <__ seg O C  \/  seg O A === seg O C              [H4];
  thus seg D F <__ seg A C

  proof
    consider K such that
    K IN int_angle A O C /\ angle D O' F === angle A O K     [KintAOC] by H1, ANGLE, H3, AngleOrderingUse;
    ~(O = C) /\ ~(D = F) /\ ~(O' = F) /\ ~(O = K)     [Distinct] by H1, NonCollinearImpliesDistinct, -, InteriorEZHelp;
    consider B such that
    B IN ray O K DELETE O  /\  seg O B === seg O C     [BrOK] by Distinct, SEGMENT, -, C1;
    ray O B = ray O K     by Distinct, -, RayWellDefined;
    angle D O' F === angle A O B     [DO'FeqAOB] by KintAOC, -, Angle_DEF;
    B IN int_angle A O C     [BintAOC] by KintAOC, BrOK, WholeRayInterior;
    ~(B = O) /\ ~Collinear A O B     [AOBncol] by -, InteriorEZHelp;
    seg O C === seg O B     [OCeqOB] by Distinct, -, SEGMENT, BrOK, C2Symmetric;
    seg O' F === seg O B     by Distinct, SEGMENT, AOBncol, H2, -, C2Transitive;
    D,O',F cong A,O,B     by H1, AOBncol, H2, -, DO'FeqAOB, SAS;
    seg D F === seg A B     [DFeqAB] by -, TriangleCong_DEF;
    consider G such that
    G IN open (A,C)  /\  G IN ray O B DELETE O  /\  ~(G = O)     [AGC] by BintAOC, Crossbar_THM, B1', IN_DELETE;
    Segment (seg O G) /\ ~(O = B)     [notOB] by AGC, SEGMENT, BrOK, IN_DELETE;
    seg O G <__ seg O C     by H1, AGC, H4, InteriorCircleConvexHelp;
    seg O G <__ seg O B     by -, OCeqOB, BrOK, IN_DELETE, SEGMENT, SegmentTrichotomy2;
    consider G' such that
    G' IN open (O,B)  /\  seg O G === seg O G'     [OG'B] by notOB, -, SegmentOrderingUse;
    ~(G' = O)  /\  seg O G' === seg O G'  /\  Segment (seg O G')     [notG'O] by -, B1', SEGMENT, C2Reflexive, SEGMENT;
    G' IN ray O B DELETE O     by OG'B, IntervalRayEZ;
    G' = G  /\  G IN open (B,O)     by notG'O, notOB, -, AGC, OG'B, C1, B1';
    ConvexQuadrilateral B A O C     by H1, -, AGC, DiagonalsIntersectImpliesConvexQuad;
    A IN int_angle O C B  /\  O IN int_angle C B A  /\  Quadrilateral B A O C     [OintCBA] by -, ConvexQuad_DEF;
    A IN int_angle B C O     [AintBCO] by -, InteriorAngleSymmetry;
    Tetralateral B A O C     by OintCBA, Quadrilateral_DEF;
    ~Collinear C B A  /\ ~Collinear B C O /\ ~Collinear C O B /\ ~Collinear C B O     [BCOncol] by -, Tetralateral_DEF, CollinearSymmetry;
    angle B C O === angle C B O     [BCOeqCBO] by -, OCeqOB, IsoscelesCongBaseAngles;
    ~Collinear B C A /\ ~Collinear A C B     [ACBncol] by AintBCO, InteriorEZHelp, CollinearSymmetry;
    angle B C A === angle B C A  /\  Angle (angle B C A)  /\  angle C B O === angle C B O     [CBOref] by -, ANGLE, BCOncol, C5Reflexive;
    angle B C A <_ang angle B C O     by -, BCOncol, ANGLE, AintBCO, AngleOrdering_DEF;
    angle B C A <_ang angle C B O     [BCAlessCBO] by -, BCOncol, ANGLE, BCOeqCBO, AngleTrichotomy2;
    angle C B O <_ang angle C B A     by BCOncol, ANGLE, OintCBA, CBOref, AngleOrdering_DEF;
    angle A C B <_ang angle C B A     by BCAlessCBO, -, AngleOrderTransitivity, AngleSymmetry;
    seg A B <__ seg A C     by ACBncol, -, EuclidPropositionI_19;
 qed     by -, Distinct, SEGMENT, DFeqAB, SegmentTrichotomy3;
`;;

let EuclidPropositionI_24 = thm `;
  let O A C O' D F be point;
  assume ~Collinear A O C /\ ~Collinear D O' F                   [H1];
  assume seg O' D === seg O A /\ seg O' F === seg O C                [H2];
  assume  angle D O' F <_ang angle A O C                                [H3];
  thus seg D F <__ seg A C

  proof
    ~(O = A) /\ ~(O = C) /\ ~Collinear C O A /\ ~Collinear F O' D     [Distinct] by H1, NonCollinearImpliesDistinct, CollinearSymmetry;
    seg O A === seg O C  \/  seg O A <__ seg O C  \/  seg O C <__ seg O A     by  -, SEGMENT, SegmentTrichotomy;
    cases by -;
      suppose seg O A <__ seg O C  \/  seg O A === seg O C;
      qed     by H1, H2, H3, -, EuclidPropositionI_24Help;
      suppose seg O C <__ seg O A     [H4];
        angle F O' D <_ang angle C O A     by H3, AngleSymmetry;
     qed     by Distinct, H3, AngleSymmetry, H2, H4, EuclidPropositionI_24Help, SegmentSymmetry;
  end;
`;;

let EuclidPropositionI_25 = thm `;
  let O A C O' D F be point;
  assume ~Collinear A O C /\ ~Collinear D O' F                   [H1];
  assume seg O' D === seg O A /\ seg O' F === seg O C                [H2];
  assume  seg D F <__ seg A C                                   [H3];
  thus angle D O' F <_ang angle A O C

  proof
    ~(O = A) /\ ~(O = C) /\ ~(A = C) /\ ~(D = F) /\ ~(O' = D) /\ ~(O' = F)     [Distinct] by H1, NonCollinearImpliesDistinct;
    assume ~(angle D O' F <_ang angle A O C);
    angle D O' F === angle A O C  \/  angle A O C <_ang angle D O' F     by H1, ANGLE, -, AngleTrichotomy;
    cases by -;
    suppose angle D O' F === angle A O C;
      D,O',F cong A,O,C     by H1, H2, -, SAS;
      seg D F === seg A C     by -, TriangleCong_DEF;
    qed     by Distinct, SEGMENT, -, H3, SegmentTrichotomy;
    suppose angle A O C <_ang angle D O' F [Con];
      seg O A === seg O' D  /\  seg O C  === seg O' F     [H2'] by Distinct, SEGMENT, H2, C2Symmetric;
      seg A C <__ seg D F     by H1, -, Con, EuclidPropositionI_24;
    qed      by Distinct, SEGMENT, -, H3, SegmentTrichotomy;
  end;
`;;

let AAS = thm `;
  let A B C A' B' C' be point;
  assume ~Collinear A B C /\ ~Collinear A' B' C'                 [H1];
  assume angle A B C === angle A' B' C'  /\  angle B C A === angle B' C' A'          [H2];
  assume seg A B === seg A' B'                                            [H3];
  thus A,B,C cong A',B',C'

  proof
    ~(A = B) /\ ~(B = C) /\ ~(B' = C')     [Distinct] by H1, NonCollinearImpliesDistinct;
    consider G such that
    G IN ray B C DELETE B /\ seg B G === seg B' C'     [Gexists] by Distinct, SEGMENT, C1;
    ~(G = B)  /\  B NOTIN open (G,C)  /\ Collinear G B C     [notGBC] by -, IN_DELETE, IN_Ray, CollinearSymmetry;
    ~Collinear A B G /\ ~Collinear B G A     [ABGncol] by H1, notGBC, CollinearSymmetry, NoncollinearityExtendsToLine;
    ray B G = ray B C     by Distinct, Gexists, RayWellDefined;
    angle A B G = angle A B C     by Distinct, -, Angle_DEF;
    A,B,G cong A',B',C'     [ABGcongA'B'C'] by H1, ABGncol, H3, SegmentSymmetry, H2, -, Gexists, SAS;
    angle B G A === angle B' C' A'     [BGAeqB'C'A'] by -, TriangleCong_DEF;
    ~Collinear B C A  /\ ~Collinear B' C' A'     [BCAncol] by H1, CollinearSymmetry;
    angle B' C' A' === angle B C A  /\  angle B C A === angle B C A     [BCArefl] by -, ANGLE, H2, C5Symmetric, C5Reflexive;
    angle B G A === angle B C A     [BGAeqBCA] by ABGncol, BCAncol, ANGLE, BGAeqB'C'A', -, C5Transitive;
    cases;
    suppose G = C;
    qed     by -, ABGcongA'B'C';
    suppose ~(G = C)     [notGC];
     ~Collinear A C G /\ ~Collinear A G C     [ACGncol] by H1, notGBC, -, CollinearSymmetry, NoncollinearityExtendsToLine;
      C IN open (B,G) \/ G IN open (C,B)     by notGBC, notGC, Distinct, B3', NOTIN;
      cases     by -;
      suppose C IN open (B,G) ;
        C IN open (G,B)  /\ ray G C = ray G B     [rGCrBG] by -, B1', IntervalRay;
        angle A G C <_ang angle A C B     by ACGncol, -, ExteriorAngle;
        angle B G A <_ang angle B C A     by -, rGCrBG, Angle_DEF, AngleSymmetry, AngleSymmetry;
      qed     by ABGncol, BCAncol, ANGLE, -, AngleSymmetry, BGAeqBCA, AngleTrichotomy;
      suppose G IN open (C,B)     [CGB];
        ray C G = ray C B  /\  angle A C G <_ang angle A G B     by -, IntervalRay, ACGncol, ExteriorAngle;
        angle A C B <_ang angle B G A     by -, Angle_DEF, AngleSymmetry;
        angle B C A <_ang angle B C A     by -, BCAncol, ANGLE, BGAeqBCA, AngleTrichotomy2, AngleSymmetry;
      qed     by -, BCArefl, AngleTrichotomy1;
    end;
  end;
`;;

let ParallelSymmetry = thm `;
  ! l k: point_set. l parallel k  ==>  k parallel l
  by PARALLEL, INTER_COMM;
`;;

let AlternateInteriorAngles = thm `;
  let A B C E be point;
  let l m t be point_set;
  assume Line l /\ A IN l /\ E IN l                                   [l_line];
  assume Line m /\ B IN m /\ C IN m                                   [m_line];
  assume Line t /\ A IN t /\ B IN t                                   [t_line];
  assume ~(A = E) /\ ~(B = C) /\ ~(A = B) /\ E NOTIN t /\ C NOTIN t           [Distinct];
  assume ~(C,E same_side t)                                        [Cnsim_tE];
  assume angle E A B === angle C B A [AltIntAngCong];
  thus l parallel m

  proof
    ~Collinear E A B /\ ~Collinear C B A     [EABncol] by t_line, Distinct, I1, Collinear_DEF, NOTIN;
    B NOTIN l /\ A NOTIN m     [notAmBl] by l_line, m_line, Collinear_DEF, -, NOTIN;
    assume ~(l parallel m);
    ~(l INTER m = {})     by -, l_line, m_line, PARALLEL;
    consider G such that
    G IN l /\ G IN m     [Glm] by -, MEMBER_NOT_EMPTY, IN_INTER;
    ~(G = A) /\ ~(G = B) /\ Collinear B G C /\ Collinear B C G /\ Collinear A E G /\ Collinear A G E     [GnotAB] by -, notAmBl, NOTIN, m_line, l_line, Collinear_DEF;
    ~Collinear A G B /\ ~Collinear B G A /\ G NOTIN t      [AGBncol]  by EABncol, CollinearSymmetry, -, NoncollinearityExtendsToLine, t_line, Collinear_DEF, NOTIN;
    ~(E,C same_side t)     [Ensim_tC] by t_line, -, Distinct, Cnsim_tE, SameSideSymmetric;
    C IN m DELETE B  /\  G IN m DELETE B     [CGm_B] by m_line, Glm, Distinct, GnotAB, IN_DELETE;
    E IN l DELETE A  /\  G IN l DELETE A     [EGm_A] by l_line, Glm, Distinct, GnotAB, IN_DELETE;
    ~(G,E same_side t)
    proof
      assume G,E same_side t     [Gsim_tE];
      A NOTIN open (G,E)     [notGAE] by t_line, -, SameSide_DEF, NOTIN;
      G IN ray A E DELETE A     by Distinct, GnotAB, notGAE, IN_Ray, GnotAB, IN_DELETE;
      ray A G = ray A E     [rAGrAE] by Distinct, -, RayWellDefined;
      ~(C,G same_side t)     by t_line, AGBncol, Distinct, Gsim_tE, Cnsim_tE, SameSideTransitive;
       C NOTIN ray B G  /\  B IN open (C,G)     by t_line, AGBncol, Distinct, -, RaySameSide, NOTIN, GnotAB, IN_DELETE, IN_Ray;
      angle G A B <_ang angle C B A     by AGBncol, -, B1', EuclidPropositionI_16;
      angle E A B <_ang angle C B A     by -, rAGrAE, Angle_DEF;
    qed     by EABncol, ANGLE, AltIntAngCong, -, AngleTrichotomy1;
    G,C same_side t     [Gsim_tC] by t_line, AGBncol, Distinct, -, Cnsim_tE, AtMost2Sides;
    :: now we make a symmetric argument
    B NOTIN open (G,C)     [notGBC] by t_line, -, SameSide_DEF, NOTIN;
    G IN ray B C DELETE B     by Distinct, GnotAB, notGBC, IN_Ray, GnotAB, IN_DELETE;
    ray B G = ray B C     [rBGrBC] by Distinct, -, RayWellDefined;
    angle C B A === angle E A B     [flipAltIntAngCong] by EABncol, ANGLE, AltIntAngCong, C5Symmetric;
    ~(E,G same_side t)     by t_line, AGBncol, Distinct, Gsim_tC, Ensim_tC, SameSideTransitive;
    E NOTIN ray A G   /\  A IN open (E,G)     by t_line, AGBncol, Distinct, -, RaySameSide, NOTIN, GnotAB, IN_Ray, IN_DELETE;
    angle G B A <_ang angle E A B     by AGBncol, -, B1', EuclidPropositionI_16;
    angle C B A <_ang angle E A B     by -, rBGrBC, Angle_DEF;
  qed     by EABncol, ANGLE, flipAltIntAngCong, -, AngleTrichotomy1;
`;;

let EuclidPropositionI_28 = thm `;
  let A B C D E F G H be point;
  let l m t be point_set;
  assume Line l /\ A IN l /\ B IN l /\ G IN l                 [l_line];
  assume Line m /\ C IN m /\ D IN m /\ H IN m                 [m_line];
  assume Line t /\ G IN t /\ H IN t                         [t_line];
  assume  G NOTIN m /\ H NOTIN l                                 [notGmHl];
  assume G IN open (A,B)  /\ H IN open (C,D)                       [H1];
  assume G IN open (E,H)  /\  H IN open (F,G)                      [H2];
  assume ~(D,A same_side t)                                     [H3];
  assume angle E G B === angle G H D  \/  angle B G H suppl angle G H D            [H4];
  thus l parallel m

  proof
    ~(A = G) /\ ~(G = B) /\ ~(H = D) /\ ~(E = G) /\ ~(G = H) /\ Collinear A G B /\ Collinear E G H     [Distinct] by H1, H2, B1';
    ~Collinear H G A /\ ~Collinear G H D /\ A NOTIN t /\ D NOTIN t     [HGAncol] by l_line, m_line, Distinct, I1, Collinear_DEF, notGmHl, NOTIN, t_line, Collinear_DEF;
    ~Collinear B G H /\ ~Collinear A G E /\ ~Collinear E G B     [BGHncol] by -, Distinct, CollinearSymmetry, NoncollinearityExtendsToLine;
    angle A G H === angle D H G
    proof
      cases     by H4;
      suppose angle E G B === angle G H D     [EGBeqGHD];
        angle E G B === angle H G A     by BGHncol, H1, H2, VerticalAnglesCong;
        angle H G A === angle E G B     by BGHncol, HGAncol, ANGLE, -, C5Symmetric;
        angle H G A === angle G H D     by BGHncol, HGAncol, ANGLE, -, EGBeqGHD, C5Transitive;
      qed     by -, AngleSymmetry;
      suppose angle B G H suppl angle G H D [BGHeqGHD];
        angle B G H suppl angle H G A     by BGHncol, H1, B1', SupplementaryAngles_DEF;
      qed     by -, BGHeqGHD, AngleSymmetry, SupplementUnique, AngleSymmetry;
    end;
  qed     by l_line, m_line, t_line, Distinct, HGAncol, H3, -,  AlternateInteriorAngles;
`;;

let OppositeSidesCongImpliesParallelogram = thm `;
  let A B C D be point;
  assume Quadrilateral A B C D                          [H1];
  assume seg A B === seg C D  /\  seg B C === seg D A        [H2];
  thus Parallelogram A B C D

  proof
    ~(A = B) /\ ~(A = C) /\ ~(A = D) /\ ~(B = C) /\ ~(B = D) /\ ~(C = D) /\
    ~Collinear A B C /\ ~Collinear B C D /\ ~Collinear C D A /\ ~Collinear D A B     [TetraABCD] by H1, Quadrilateral_DEF, Tetralateral_DEF;
    consider a c such that
    Line a /\ A IN a /\ B IN a   /\
    Line c /\ C IN c /\ D IN c     [ac_line] by TetraABCD, I1;
    consider b d such that
    Line b /\ B IN b /\ C IN b   /\
    Line d /\ D IN d /\ A IN d     [bd_line] by TetraABCD, I1;
    consider l such that
    Line l /\ A IN l /\ C IN l     [l_line] by TetraABCD, I1;
    consider m such that
    Line m /\ B IN m /\ D IN m     [m_line] by TetraABCD, I1;
    B NOTIN l /\ D NOTIN l /\ A NOTIN m  /\ C NOTIN m     [notBDlACm] by l_line, m_line, TetraABCD, Collinear_DEF, NOTIN;
    seg A C === seg C A  /\  seg B D === seg D B     [seg_refl] by TetraABCD, SEGMENT, C2Reflexive, SegmentSymmetry;
    A,B,C cong C,D,A     by TetraABCD, H2, -, SSS;
    angle B C A === angle D A C  /\  angle C A B === angle A C D     [BCAeqDAC] by -, TriangleCong_DEF;
    seg C D === seg A B     [CDeqAB] by TetraABCD, SEGMENT, H2, C2Symmetric;
    B,C,D cong D,A,B     by TetraABCD, H2, -, seg_refl, SSS;
    angle C D B === angle A B D  /\  angle D B C === angle B D A     [CDBeqABD] by -, TriangleCong_DEF;
    ~(B,D same_side l)  \/  ~(A,C same_side m)     by H1, l_line, m_line, FiveChoicesQuadrilateral;
    cases     by -;
    suppose ~(B,D same_side l);
      ~(D,B same_side l)     by l_line, notBDlACm, -, SameSideSymmetric;
      a parallel c  /\  b parallel d     by ac_line, l_line, TetraABCD, notBDlACm, -, BCAeqDAC, AngleSymmetry, AlternateInteriorAngles, bd_line, BCAeqDAC;
    qed     by H1, ac_line, bd_line, -, Parallelogram_DEF;
    suppose ~(A,C same_side m);
      b parallel d  /\  c parallel a     by bd_line, m_line, TetraABCD, notBDlACm, -, CDBeqABD, AngleSymmetry, AlternateInteriorAngles, ac_line, CDBeqABD;
    qed     by H1, ac_line, bd_line, -, ParallelSymmetry, Parallelogram_DEF;
  end;
`;;

let OppositeAnglesCongImpliesParallelogramHelp = thm `;
  let A B C D be point;
  let a c be point_set;
  assume Quadrilateral A B C D                          [H1];
  assume angle A B C === angle C D A  /\  angle D A B === angle B C D        [H2];
  assume Line a /\ A IN a /\ B IN a                 [a_line];
  assume Line c  /\ C IN c /\ D IN c                        [c_line];
  thus a parallel c

  proof
    ~(A = B) /\ ~(A = C) /\ ~(A = D) /\ ~(B = C) /\ ~(B = D) /\ ~(C = D) /\
    ~Collinear A B C /\ ~Collinear B C D /\ ~Collinear C D A /\ ~Collinear D A B     [TetraABCD] by H1, Quadrilateral_DEF, Tetralateral_DEF;
    angle C D A === angle A B C  /\  angle B C D === angle D A B     [H2'] by TetraABCD, ANGLE, H2, C5Symmetric;
    consider l m such that
    Line l /\ A IN l /\ C IN l  /\
    Line m /\ B IN m /\ D IN m     [lm_line] by TetraABCD, I1;
    consider b d such that
    Line b /\ B IN b /\ C IN b   /\  Line d /\ D IN d /\ A IN d     [bd_line] by TetraABCD, I1;
    A NOTIN c /\ B NOTIN c /\ A NOTIN b /\ D NOTIN b /\ B NOTIN d /\ C NOTIN d     [point_off_line] by c_line, bd_line, Collinear_DEF, TetraABCD, NOTIN;
    ~(A IN int_triangle B C D  \/  B IN int_triangle C D A  \/
    C IN int_triangle D A B  \/  D IN int_triangle A B C)
    proof
      assume A IN int_triangle B C D  \/  B IN int_triangle C D A  \/
      C IN int_triangle D A B  \/  D IN int_triangle A B C;
      angle B C D <_ang angle D A B  \/  angle C D A <_ang angle A B C  \/
      angle D A B <_ang angle B C D  \/  angle A B C <_ang angle C D A     by TetraABCD, -, EuclidPropositionI_21;
    qed     by -, H2', H2, AngleTrichotomy1;
    ConvexQuadrilateral A B C D     by H1, lm_line, -, FiveChoicesQuadrilateral;
    A IN int_angle B C D  /\  B IN int_angle C D A  /\
    C IN int_angle D A B  /\  D IN int_angle A B C     [AintBCD] by -, ConvexQuad_DEF;
    B,A same_side c  /\  B,C same_side d     [Bsim_cA] by c_line, bd_line, -, InteriorUse;
    A,D same_side b     [Asim_bD] by bd_line, c_line, AintBCD, InteriorUse;
    assume ~(a parallel c);
    consider G such that
    G IN a /\ G IN c     [Gac] by -, a_line, c_line, PARALLEL, MEMBER_NOT_EMPTY, IN_INTER;
    Collinear A B G /\ Collinear D G C /\ Collinear C G D     [ABGcol] by a_line, -, Collinear_DEF, c_line;
    ~(G = A) /\ ~(G = B) /\ ~(G = C) /\ ~(G = D)     [GnotABCD] by Gac, ABGcol, TetraABCD, CollinearSymmetry, Collinear_DEF;
    ~Collinear B G C /\ ~Collinear A D G     [BGCncol] by c_line, Gac, GnotABCD, I1, Collinear_DEF, point_off_line, NOTIN;
    ~Collinear B C G /\ ~Collinear G B C /\ ~Collinear G A D /\ ~Collinear A G D     [BCGncol] by -, CollinearSymmetry;
    G NOTIN b /\ G NOTIN d     [notGb] by bd_line, Collinear_DEF, BGCncol, NOTIN;
    G NOTIN open (B,A)     [notBGA] by Bsim_cA, Gac, SameSide_DEF, NOTIN;
    B NOTIN open (A,G)     [notABG]
    proof
      assume ~(B NOTIN open (A,G));
      B IN open (A,G)     [ABG] by -, NOTIN;
      ray A B = ray A G     [rABrAG] by -, IntervalRay;
      ~(A,G same_side b)     by bd_line, ABG, SameSide_DEF;
      ~(D,G same_side b)     by bd_line, point_off_line, notGb, Asim_bD, -, SameSideTransitive;
      D NOTIN ray C G     by bd_line, notGb, -, RaySameSide, TetraABCD, IN_DELETE, NOTIN;
      C IN open (D,G)     [DCG] by GnotABCD, ABGcol, -, IN_Ray, NOTIN;
      consider M such that
      D IN open (C,M)     [CDM] by TetraABCD, B2';
      D IN open (G,M)     [GDM] by -, B1', DCG, TransitivityBetweennessHelp;
      angle C D A suppl angle A D M  /\  angle A B C suppl angle C B G     by TetraABCD, CDM, ABG, SupplementaryAngles_DEF;
      angle M D A === angle G B C     [MDAeqGBC] by -, H2', SupplementsCongAnglesCong, AngleSymmetry;
      angle G A D <_ang angle M D A  /\  angle G B C <_ang angle D C B     by BCGncol, BGCncol, GDM, DCG, B1', EuclidPropositionI_16;
      angle G A D <_ang angle D C B     by  -, BCGncol, ANGLE, MDAeqGBC, AngleTrichotomy2, AngleOrderTransitivity;
      angle D A B <_ang angle B C D     by -, rABrAG, Angle_DEF, AngleSymmetry;
    qed     by -, H2, AngleTrichotomy1;
    A NOTIN open (G,B)
    proof
      assume ~(A NOTIN open (G,B));
      A IN open (B,G)     [BAG] by -, B1', NOTIN;
      ray B A = ray B G     [rBArBG] by -, IntervalRay;
      ~(B,G same_side d)     by bd_line, BAG, SameSide_DEF;
      ~(C,G same_side d)     by bd_line, point_off_line, notGb, Bsim_cA, -,  SameSideTransitive;
      C NOTIN ray D G     by bd_line, notGb, -, RaySameSide, TetraABCD, IN_DELETE, NOTIN;
      D IN open (C,G)     [CDG] by GnotABCD, ABGcol, -, IN_Ray, NOTIN;
      consider M such that
      C IN open (D,M)     [DCM] by B2', TetraABCD;
      C IN open (G,M)     [GCM] by -, B1', CDG, TransitivityBetweennessHelp;
      angle B C D suppl angle M C B  /\  angle D A B suppl angle G A D     by TetraABCD, CollinearSymmetry, DCM, BAG, SupplementaryAngles_DEF, AngleSymmetry;
      angle M C B === angle G A D     [GADeqMCB] by -, H2', SupplementsCongAnglesCong;
      angle G B C <_ang angle M C B  /\  angle G A D <_ang angle C D A     by BGCncol, GCM, BCGncol, CDG, B1', EuclidPropositionI_16;
      angle G B C <_ang angle C D A     by -, BCGncol, ANGLE, GADeqMCB, AngleTrichotomy2, AngleOrderTransitivity;
      angle A B C <_ang angle C D A     by -, rBArBG, Angle_DEF;
    qed     by -, H2, AngleTrichotomy1;
  qed     by TetraABCD, GnotABCD, ABGcol, notABG, notBGA, -, B3', NOTIN;
`;;

let OppositeAnglesCongImpliesParallelogram = thm `;
  let A B C D be point;
  assume Quadrilateral A B C D                          [H1];
  assume angle A B C === angle C D A  /\  angle D A B === angle B C D        [H2];
  thus Parallelogram A B C D

  proof
    Quadrilateral B C D A     [QuadBCDA] by H1, QuadrilateralSymmetry;
    ~(A = B) /\ ~(B = C) /\ ~(C = D) /\ ~(D = A) /\ ~Collinear B C D /\ ~Collinear D A B     [TetraABCD] by H1, Quadrilateral_DEF, Tetralateral_DEF;
    angle B C D === angle D A B     [H2'] by TetraABCD, ANGLE, H2, C5Symmetric;
    consider a such that
    Line a /\ A IN a /\ B IN a     [a_line] by TetraABCD, I1;
    consider b such that
    Line b /\ B IN b /\ C IN b     [b_line] by TetraABCD, I1;
    consider c such that
    Line c  /\ C IN c /\ D IN c     [c_line] by TetraABCD, I1;
    consider d such that
    Line d /\ D IN d /\ A IN d     [d_line] by TetraABCD, I1;
  qed     by H1, QuadBCDA, H2, H2', a_line, b_line, c_line, d_line, OppositeAnglesCongImpliesParallelogramHelp, Parallelogram_DEF;
`;;


let P = new_axiom
  `! P l. Line l /\ P NOTIN l  ==> ?! m. Line m /\ P IN m /\ m parallel l`;;

new_constant("mu",`:point_set->real`);;

let AMa = new_axiom
 `! alpha. Angle alpha  ==>  &0 < mu alpha /\ mu alpha < &180`;;

let AMb = new_axiom
 `! alpha. Right alpha  ==>  mu alpha  = &90`;;

let AMc = new_axiom
 `! alpha beta. Angle alpha /\ Angle beta /\ alpha === beta  ==>  mu alpha = mu beta`;;

let AMd = new_axiom
 `! A O B P. P IN int_angle A O B  ==>  mu (angle A O B) = mu (angle A O P) + mu (angle P O B)`;;


let ConverseAlternateInteriorAngles = thm `;
  let A B C E be point;
  let l m t be point_set;
  assume Line l /\ A IN l /\ E IN l                                   [l_line];
  assume Line m /\ B IN m /\ C IN m                                   [m_line];
  assume Line t /\ A IN t /\ B IN t                                   [t_line];
  assume ~(A = E) /\ ~(B = C) /\ ~(A = B) /\ E NOTIN t /\ C NOTIN t           [Distinct];
  assume ~(C,E same_side t)                                        [Cnsim_tE];
  assume l parallel m                                                     [para_lm];
  thus angle E A B === angle C B A

  proof
    ~Collinear C B A     by t_line, Distinct, I1, Collinear_DEF, NOTIN, ANGLE;
    A NOTIN m /\ Angle (angle C B A)     [notAm] by m_line, -, Collinear_DEF, NOTIN, ANGLE;
    consider D such that
    ~(A = D) /\ D NOTIN t /\ ~(C,D same_side t) /\ seg A D === seg A E  /\  angle B A D === angle C B A     [Dexists] by -,  Distinct, t_line, C4OppositeSide;
    consider k such that
    Line k /\ A IN k /\ D IN k     [k_line] by Distinct, I1;
    k parallel m     by -, m_line, t_line, Dexists, Distinct, AngleSymmetry, AlternateInteriorAngles;
    k = l     by m_line, notAm, l_line, k_line, -, para_lm, P;
    D,E same_side t  /\  A NOTIN open (D,E)  /\  Collinear A E D     by t_line, Distinct, Dexists, Cnsim_tE, AtMost2Sides, SameSide_DEF, NOTIN, -, k_line, l_line, Collinear_DEF;
    ray A D = ray A E     by Distinct, -, IN_Ray, Dexists, IN_DELETE, RayWellDefined;
  qed     by -, Dexists, AngleSymmetry, Angle_DEF;
`;;

let HilbertTriangleSum = thm `;
  let A B C be point;
  assume ~Collinear A B C                               [ABCncol];
  thus ? E F. B IN open (E,F)  /\  C IN int_angle A B F  /\
           angle E B A === angle C A B  /\  angle C B F === angle B C A

  proof
    ~(A = B) /\ ~(A = C) /\ ~(B = C) /\ ~Collinear C A B     [Distinct] by ABCncol, NonCollinearImpliesDistinct, CollinearSymmetry;
    consider l such that
    Line l /\ A IN l /\ C IN l     [l_line] by Distinct, I1;
    consider x such that
    Line x /\ A IN x /\ B IN x     [x_line] by Distinct, I1;
    consider y such that
    Line y /\ B IN y /\ C IN y     [y_line] by Distinct, I1;
    C NOTIN x     [notCx] by x_line, ABCncol, Collinear_DEF, NOTIN;
    Angle (angle C A B)     by ABCncol, CollinearSymmetry, ANGLE;
    consider E such that
    ~(B = E) /\ E NOTIN x /\ ~(C,E same_side x) /\ seg B E === seg A B /\ angle A B E === angle C A B     [Eexists] by -, Distinct, x_line, notCx, C4OppositeSide;
    consider m such that
    Line m /\ B IN m /\ E IN m     [m_line] by -, I1, IN_DELETE;
    angle E B A === angle C A B     [EBAeqCAB] by Eexists, AngleSymmetry;
    m parallel l     [para_lm] by m_line, l_line, x_line, Eexists, Distinct, notCx, -, AlternateInteriorAngles;
    m INTER l = {}     [lm0] by -, PARALLEL;
    C NOTIN m /\ A NOTIN m     [notACm] by -, l_line, INTER_COMM, DisjointOneNotOther;
    consider F such that
    B IN open (E,F)     [EBF] by Eexists, B2';
    ~(B = F) /\ F IN m     [EBF'] by -, B1', m_line, BetweenLinear;
    ~Collinear A B F /\ F NOTIN x      [ABFncol] by m_line, -, I1, Collinear_DEF, notACm, NOTIN, x_line;
    ~(E,F same_side x) /\ ~(E,F same_side y)     [Ensim_yF] by EBF, x_line, y_line, SameSide_DEF;
    C,F same_side x     [Csim_xF] by x_line, notCx, Eexists, ABFncol, Eexists, -, AtMost2Sides;
    m INTER open(C,A)  =  {}     by l_line, BetweenLinear, SUBSET, SET_RULE, lm0, SUBSET_EMPTY;
    C,A same_side m     by m_line, -, SameSide_DEF, SET_RULE;
    C IN int_angle A B F     [CintABF] by ABFncol, x_line, m_line, EBF', notCx, notACm, Csim_xF, -, IN_InteriorAngle;
    A IN int_angle C B E     by EBF, B1', -, InteriorAngleSymmetry, InteriorReflectionInterior;
    A NOTIN y  /\  A,E same_side y     [Asim_yE] by y_line, m_line, -, InteriorUse;
    E NOTIN y /\ F NOTIN y     [notEFy] by y_line, m_line, EBF', Eexists, EBF', I1, Collinear_DEF, notACm, NOTIN;
    E,A same_side y  by y_line, -, Asim_yE, SameSideSymmetric;
    ~(A,F same_side y)     [Ansim_yF] by y_line, notEFy, Asim_yE, -, Ensim_yF, SameSideTransitive;
    angle F B C === angle A C B     by m_line, EBF', l_line, y_line, EBF', Distinct, notEFy, Asim_yE, Ansim_yF, para_lm, ConverseAlternateInteriorAngles;
  qed     by EBF, CintABF, EBAeqCAB, -, AngleSymmetry;
`;;

let EuclidPropositionI_13 = thm `;
  let A O B A' be point;
  assume ~Collinear A O B                       [H1];
  assume O IN open (A,A')                        [H2];
  thus mu (angle A O B) + mu (angle B O A') = &180

  proof
    cases;
    suppose Right (angle A O B);
      Right (angle B O A')  /\  mu (angle A O B) = &90  /\  mu (angle B O A') = &90     by H1, H2, -, RightImpliesSupplRight, AMb;
    qed by -, REAL_ARITH;
    suppose ~Right (angle A O B)     [notRightAOB];
      ~(A = O) /\ ~(O = B)     [Distinct] by H1, NonCollinearImpliesDistinct;
      consider l such that
      Line l /\ O IN l /\ A IN l /\ A' IN l     [l_line] by -, I1, H2, BetweenLinear;
      B NOTIN l     [notBl] by -, Distinct, I1, Collinear_DEF, H1, NOTIN;
      consider F such that
      Right (angle O A F)  /\  Angle (angle O A F)     [RightOAF] by Distinct, EuclidPropositionI_11, RightImpliesAngle;
      ?! r. Ray r /\ ? E. ~(O = E) /\ r = ray O E /\ E NOTIN l /\ E,B same_side l /\ angle A O E === angle O A F     by -, Distinct, l_line, notBl, C4;
      consider E such that
      ~(O = E)  /\  E NOTIN l  /\  E,B same_side l  /\  angle A O E === angle O A F     [Eexists] by -;
      ~Collinear A O E     [AOEncol] by l_line, Distinct, I1, Collinear_DEF, -, NOTIN;
      Right (angle A O E)     [RightAOE] by -, ANGLE, RightOAF, Eexists, CongRightImpliesRight;
      Right (angle E O A')  /\  mu (angle A O E) = &90  /\  mu (angle E O A') = &90     [RightEOA'] by AOEncol, H2, -,  RightImpliesSupplRight, AMb;
      ~(angle A O B === angle A O E)     by notRightAOB, H1, ANGLE, RightAOE, CongRightImpliesRight;
      ~(angle A O B = angle A O E)     by H1, AOEncol, ANGLE, -, C5Reflexive;
      ~(ray O B = ray O E)     by -, Angle_DEF;
      B NOTIN ray O E  /\  O NOTIN open (B,E)     by Distinct, -, Eexists, RayWellDefined, IN_DELETE, NOTIN, l_line, B1', SameSide_DEF;
      ~Collinear O E B     by -, Eexists, IN_Ray, NOTIN;
      E IN int_angle A O B  \/  B IN int_angle A O E     by Distinct, l_line, Eexists, notBl, AngleOrdering, -, CollinearSymmetry, InteriorAngleSymmetry;
      cases by -;
      suppose E IN int_angle A O B     [EintAOB];
        B IN int_angle E O A'     by H2, -, InteriorReflectionInterior;
        mu (angle A O B) = mu (angle A O E) + mu (angle E O B)  /\
        mu (angle E O A') = mu (angle E O B) + mu (angle B O A')     by EintAOB, -, AMd;
      qed     by -, RightEOA', REAL_ARITH;
      suppose B IN int_angle A O E     [BintAOE];
        E IN int_angle B O A'     by H2, -, InteriorReflectionInterior;
        mu (angle A O E) = mu (angle A O B) + mu (angle B O E)  /\
        mu (angle B O A') = mu (angle B O E) + mu (angle E O A')     by BintAOE, -, AMd;
      qed     by -, RightEOA', REAL_ARITH;
    end;
  end;
`;;

let TriangleSum = thm `;
  let A B C be point;
  assume ~Collinear A B C                               [ABCncol];
  thus mu (angle A B C) + mu (angle B C A) + mu (angle C A B) = &180

  proof
    ~Collinear C A B  /\  ~Collinear B C A     [CABncol] by ABCncol, CollinearSymmetry;
    consider E F such that
    B IN open (E,F)  /\  C IN int_angle A B F  /\  angle E B A === angle C A B  /\  angle C B F === angle B C A     [EBF] by ABCncol, HilbertTriangleSum;
    ~Collinear C B F  /\  ~Collinear A B F  /\  Collinear E B F  /\  ~(B = E)     [CBFncol] by -, InteriorAngleSymmetry, InteriorEZHelp, IN_InteriorAngle, B1', CollinearSymmetry;
    ~Collinear E B A     [EBAncol] by CollinearSymmetry, -, NoncollinearityExtendsToLine;
    mu (angle A B F) = mu (angle A B C) + mu (angle C B F)     [muCintABF] by EBF, AMd;
    mu (angle E B A) + mu (angle A B F) = &180     [suppl180] by EBAncol, EBF, EuclidPropositionI_13;
    mu (angle C A B) = mu (angle E B A)  /\  mu (angle B C A) = mu (angle C B F)     by CABncol, EBAncol, CBFncol, ANGLE, EBF, AMc;
  qed     by suppl180, muCintABF, -, REAL_ARITH;
`;;

