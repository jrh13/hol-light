(* ========================================================================= *)
(*            HOL Light Hilbert geometry axiomatic proofs                    *)
(*                                                                           *)
(*                (c) Copyright, Bill Richter 2013                           *)
(*          Distributed under the same license as HOL Light                  *)
(*                                                                           *)
(* High school students can learn rigorous axiomatic geometry proofs, as in  *)
(* http://www.math.northwestern.edu/~richter/hilbert.pdf, using Hilbert's    *)
(* axioms, and code up readable formal proofs like these here. Thanks to the *)
(* Mizar folks for their influential language, Freek Wiedijk for his dialect *)
(* miz3 of HOL Light, John Harrison for explaining how to port Mizar code to *)
(* miz3 and writing the first 100+ lines of code here, the hol-info list for *)
(* explaining features of HOL, and Benjamin Kordesh for carefully reading    *)
(* much of the paper and the code.  Formal proofs are given for the first 7  *)
(* sections of the paper, the results cited there from Greenberg's book, and *)
(* most of Euclid's book I propositions up to Proposition I.29, following    *)
(* Hartshorne, whose book seems the most exciting axiomatic geometry text.   *)
(* A proof assistant is an invaluable tool to help read it, as Hartshorne's  *)
(* proofs are often sketchy and even have gaps.                              *)
(*                                                                           *)
(* M. Greenberg, Euclidean and non-Euclidean geometries, Freeman, 1974.      *)
(* R. Hartshorne, Geometry, Euclid and Beyond, UTM series, Springer, 2000.   *)
(* ========================================================================= *)

needs "RichterHilbertAxiomGeometry/readable.ml";;

new_type("point", 0);;
NewConstant("Between", `:point->point->point->bool`);;
NewConstant("Line", `:(point->bool)->bool`);;
NewConstant("≡", `:(point->bool)->(point->bool)->bool`);;

ParseAsInfix("≅", (12, "right"));;
ParseAsInfix("same_side", (12, "right"));;
ParseAsInfix("≡", (12, "right"));;
ParseAsInfix("<__", (12, "right"));;
ParseAsInfix("<_ang", (12, "right"));;
ParseAsInfix("suppl", (12, "right"));;
ParseAsInfix("∉", (11, "right"));;
ParseAsInfix("∥", (12, "right"));;

let NOTIN = NewDefinition `;
  ∀a l. a ∉ l ⇔ ¬(a ∈ l)`;;

let INTER_TENSOR = theorem `;
  ∀s s' t t'.  s ⊂ s' ∧ t ⊂ t'  ⇒  s ∩ t ⊂ s' ∩ t'
  by set`;;

let Interval_DEF = NewDefinition `;
  ∀A B. Open (A, B) = {X | Between A X B}`;;

let Collinear_DEF = NewDefinition `;
  Collinear A B C  ⇔
  ∃l. Line l ∧ A ∈ l ∧ B ∈ l ∧ C ∈ l`;;

let SameSide_DEF = NewDefinition `;
  A,B same_side l  ⇔
  Line l ∧ ¬ ∃X.  X ∈ l  ∧  X ∈ Open (A, B)`;;

let Ray_DEF = NewDefinition `;
  ∀A B. ray A B = {X | ¬(A = B) ∧ Collinear A B X ∧ A ∉ Open (X, B)}`;;

let Ordered_DEF = NewDefinition `;
  ordered A B C D  ⇔
  B ∈ Open (A, C) ∧ B ∈ Open (A, D) ∧ C ∈ Open (A, D) ∧ C ∈ Open (B, D)`;;

let InteriorAngle_DEF = NewDefinition `;
  ∀A O B.  int_angle A O B =
    {P | ¬Collinear A O B ∧ ∃a b.
               Line a ∧ O ∈ a ∧ A ∈ a ∧ Line b ∧ O ∈ b ∧ B ∈ b ∧
               P ∉ a ∧ P ∉ b ∧ P,B same_side a ∧ P,A same_side b}`;;

let InteriorTriangle_DEF = NewDefinition `;
  ∀A B C.  int_triangle A B C =
    {P | P ∈ int_angle A B C  ∧
         P ∈ int_angle B C A  ∧
         P ∈ int_angle C A B}`;;

let Tetralateral_DEF = NewDefinition `;
  Tetralateral A B C D  ⇔
  ¬(A = B) ∧ ¬(A = C) ∧ ¬(A = D) ∧ ¬(B = C) ∧ ¬(B = D) ∧ ¬(C = D) ∧
  ¬Collinear A B C ∧ ¬Collinear B C D ∧ ¬Collinear C D A ∧ ¬Collinear D A B`;;

let Quadrilateral_DEF = NewDefinition `;
  Quadrilateral A B C D  ⇔
  Tetralateral A B C D ∧
  Open (A, B) ∩ Open (C, D) = ∅ ∧
  Open (B, C) ∩ Open (D, A) = ∅`;;

let ConvexQuad_DEF = NewDefinition `;
  ConvexQuadrilateral A B C D  ⇔
  Quadrilateral A B C D ∧
  A ∈ int_angle B C D ∧ B ∈ int_angle C D A ∧ C ∈ int_angle D A B ∧ D ∈ int_angle A B C`;;

let Segment_DEF = NewDefinition `;
  seg A B = {A, B} ∪ Open (A, B)`;;

let SEGMENT = NewDefinition `;
  Segment s  ⇔  ∃A B. s = seg A B ∧ ¬(A = B)`;;

let SegmentOrdering_DEF = NewDefinition `;
  s <__ t   ⇔
  Segment s ∧
  ∃C D X. t = seg C D ∧ X ∈ Open (C, D) ∧ s ≡ seg C X`;;

let Angle_DEF = NewDefinition `;
  ∡ A O B = ray O A ∪ ray O B`;;

let ANGLE = NewDefinition `;
  Angle α  ⇔  ∃A O B. α = ∡ A O B ∧ ¬Collinear A O B`;;

let AngleOrdering_DEF = NewDefinition `;
  α <_ang β  ⇔
  Angle α ∧
  ∃A O B G. ¬Collinear A O B  ∧  β = ∡ A O B ∧
             G ∈ int_angle A O B  ∧  α ≡ ∡ A O G`;;

let RAY = NewDefinition `;
  Ray r  ⇔  ∃O A. ¬(O = A) ∧ r = ray O A`;;

let TriangleCong_DEF = NewDefinition `;
  ∀A B C A' B' C'. (A, B, C) ≅ (A', B', C')  ⇔
  ¬Collinear A B C ∧ ¬Collinear A' B' C' ∧
  seg A B ≡ seg A' B' ∧ seg A C ≡ seg A' C' ∧ seg B C ≡ seg B' C' ∧
  ∡ A B C ≡ ∡ A' B' C' ∧
  ∡ B C A ≡ ∡ B' C' A' ∧
  ∡ C A B ≡ ∡ C' A' B'`;;

let SupplementaryAngles_DEF = NewDefinition `;
  ∀α β. α suppl β   ⇔
  ∃A O B A'. ¬Collinear A O B  ∧  O ∈ Open (A, A')  ∧  α = ∡ A O B  ∧  β = ∡ B O A'`;;

let RightAngle_DEF = NewDefinition `;
  ∀α. Right α  ⇔  ∃β. α suppl β ∧ α ≡ β`;;

let PlaneComplement_DEF = NewDefinition `;
  ∀α. complement α = {P | P ∉ α}`;;

let CONVEX = NewDefinition `;
  Convex α  ⇔  ∀A B. A ∈ α ∧ B ∈ α  ⇒ Open (A, B) ⊂ α`;;

let PARALLEL = NewDefinition `;
  ∀l k. l ∥ k   ⇔
  Line l ∧ Line k ∧ l ∩ k = ∅`;;

let Parallelogram_DEF = NewDefinition `;
  ∀A B C D. Parallelogram A B C D  ⇔
  Quadrilateral A B C D ∧ ∃a b c d.
  Line a ∧ A ∈ a ∧ B ∈ a ∧
  Line b ∧ B ∈ b ∧ C ∈ b ∧
  Line c  ∧ C ∈ c ∧ D ∈ d ∧
  Line d ∧ D ∈ d ∧ A ∈ d ∧
  a ∥ c  ∧  b ∥ d`;;

let InteriorCircle_DEF = NewDefinition `;
  ∀O R.  int_circle O R = {P | ¬(O = R) ∧ (P = O  ∨  seg O P <__ seg O R)}
`;;


(* ------------------------------------------------------------------------- *)
(* Hilbert's geometry axioms, except the parallel axiom P, defined later.    *)
(* ------------------------------------------------------------------------- *)

let I1 = NewAxiom
  `;∀A B.  ¬(A = B) ⇒ ∃! l. Line l ∧  A ∈ l ∧ B ∈ l`;;

let I2 = NewAxiom
  `;∀l. Line l  ⇒  ∃A B. A ∈ l ∧ B ∈ l ∧ ¬(A = B)`;;

let I3 = NewAxiom
  `;∃A B C. ¬(A = B) ∧ ¬(A = C) ∧ ¬(B = C) ∧
                             ¬Collinear A B C`;;

let B1 = NewAxiom
  `;∀A B C. Between A B C ⇒ ¬(A = B) ∧ ¬(A = C) ∧ ¬(B = C) ∧
            Between C B A ∧ Collinear A B C`;;

let B2 = NewAxiom
  `;∀A B. ¬(A = B) ⇒ ∃C. Between A B C`;;

let B3 = NewAxiom
  `;∀A B C. ¬(A = B) ∧ ¬(A = C) ∧ ¬(B = C) ∧ Collinear A B C
    ⇒ (Between A B C ∨ Between B C A ∨ Between C A B) ∧
        ¬(Between A B C ∧ Between B C A) ∧
        ¬(Between A B C ∧ Between C A B) ∧
        ¬(Between B C A ∧ Between C A B)`;;

let B4 = NewAxiom
  `;∀l A B C. Line l ∧ ¬Collinear A B C ∧
   A ∉ l ∧ B ∉ l ∧ C ∉ l ∧
   (∃X. X ∈ l ∧ Between A X C) ⇒
   (∃Y. Y ∈ l ∧ Between A Y B) ∨ (∃Y. Y ∈ l ∧ Between B Y C)`;;

let C1 = NewAxiom
  `;∀s O Z. Segment s ∧ ¬(O = Z)  ⇒
   ∃! P. P ∈ ray O Z ━ {O}  ∧  seg O P ≡ s`;;

let C2Reflexive = NewAxiom
  `;Segment s  ⇒  s ≡ s`;;

let C2Symmetric = NewAxiom
  `;Segment s ∧ Segment t ∧ s ≡ t  ⇒  t ≡ s`;;

let C2Transitive = NewAxiom
  `;Segment s ∧ Segment t ∧ Segment u ∧
   s ≡ t ∧ t ≡ u ⇒  s ≡ u`;;

let C3 = NewAxiom
  `;∀A B C A' B' C'.  B ∈ Open (A, C) ∧ B' ∈ Open (A', C') ∧
  seg A B ≡ seg A' B' ∧ seg B C ≡ seg B' C'  ⇒
  seg A C ≡ seg A' C'`;;

let C4 = NewAxiom
 `;∀α O A l Y. Angle α ∧ ¬(O = A) ∧ Line l ∧ O ∈ l ∧ A ∈ l ∧ Y ∉ l
    ⇒ ∃! r. Ray r  ∧  ∃B. ¬(O = B)  ∧  r = ray O B  ∧
          B ∉ l  ∧  B,Y same_side l  ∧  ∡ A O B ≡ α`;;

let C5Reflexive = NewAxiom
  `;Angle α  ⇒  α ≡ α`;;

let C5Symmetric = NewAxiom
  `;Angle α ∧ Angle β ∧ α ≡ β  ⇒  β ≡ α`;;

let C5Transitive = NewAxiom
  `;Angle α ∧ Angle β ∧ Angle γ ∧
   α ≡ β ∧ β ≡ γ ⇒  α ≡ γ`;;

let C6 = NewAxiom
  `;∀A B C A' B' C'. ¬Collinear A B C ∧ ¬Collinear A' B' C' ∧
   seg B A ≡ seg B' A' ∧ seg B C ≡ seg B' C' ∧ ∡ A B C ≡ ∡ A' B' C'
   ⇒ ∡ B C A ≡ ∡ B' C' A'`;;


(* ----------------------------------------------------------------- *)
(* Theorems.                                                         *)
(* ----------------------------------------------------------------- *)

let IN_Interval = theorem `;
  ∀A B X. X ∈ Open (A, B)  ⇔  Between A X B
  by rewrite Interval_DEF IN_ELIM_THM`;;

let IN_Ray = theorem `;
  ∀A B X. X ∈ ray A B  ⇔  ¬(A = B) ∧ Collinear A B X ∧ A ∉ Open (X, B)
  by rewrite Ray_DEF IN_ELIM_THM`;;

let IN_InteriorAngle = theorem `;
  ∀A O B P. P ∈ int_angle A O B  ⇔
    ¬Collinear A O B ∧ ∃a b.
    Line a ∧ O ∈ a ∧ A ∈ a ∧ Line b ∧ O ∈ b ∧ B ∈ b ∧
    P ∉ a ∧ P ∉ b ∧ P,B same_side a ∧ P,A same_side b
  by rewrite InteriorAngle_DEF IN_ELIM_THM`;;

let IN_InteriorTriangle = theorem `;
  ∀A B C P. P ∈ int_triangle A B C  ⇔
    P ∈ int_angle A B C  ∧  P ∈ int_angle B C A  ∧  P ∈ int_angle C A B
  by rewrite InteriorTriangle_DEF IN_ELIM_THM`;;

let IN_PlaneComplement = theorem `;
  ∀α. ∀P. P ∈ complement α  ⇔  P ∉ α
  by rewrite PlaneComplement_DEF IN_ELIM_THM`;;

let IN_InteriorCircle = theorem `;
  ∀O R P. P ∈ int_circle O R  ⇔
    ¬(O = R) ∧ (P = O  ∨  seg O P <__ seg O R)
  by rewrite InteriorCircle_DEF IN_ELIM_THM`;;

let B1' = theorem `;
  ∀A B C.  B ∈ Open (A, C) ⇒ ¬(A = B) ∧ ¬(A = C) ∧ ¬(B = C) ∧
            B ∈ Open (C, A) ∧ Collinear A B C
  by fol IN_Interval B1`;;

let B2' = theorem `;
  ∀A B. ¬(A = B) ⇒ ∃C.  B ∈ Open (A, C)
  by fol IN_Interval B2`;;

let B3' = theorem `;
  ∀A B C. ¬(A = B) ∧ ¬(A = C) ∧ ¬(B = C) ∧ Collinear A B C
    ⇒ (B ∈ Open (A, C) ∨ C ∈ Open (B, A) ∨ A ∈ Open (C, B)) ∧
       ¬(B ∈ Open (A, C) ∧ C ∈ Open (B, A)) ∧
       ¬(B ∈ Open (A, C) ∧ A ∈ Open (C, B)) ∧
       ¬(C ∈ Open (B, A) ∧ A ∈ Open (C, B))
  by fol IN_Interval B3`;;

let B4' = theorem `;
  ∀l A B C. Line l ∧ ¬Collinear A B C ∧
    A ∉ l ∧ B ∉ l ∧ C ∉ l ∧
    (∃X. X ∈ l ∧  X ∈ Open (A, C)) ⇒
    (∃Y. Y ∈ l ∧  Y ∈ Open (A, B)) ∨ (∃Y. Y ∈ l ∧  Y ∈ Open (B, C))
  by rewrite IN_Interval B4`;;

let B4'' = theorem `;
  ∀l A B C.
  Line l ∧ ¬Collinear A B C ∧ A ∉ l ∧ B ∉ l ∧ C ∉ l  ∧
  A,B same_side l  ∧  B,C same_side l  ⇒  A,C same_side l
  proof
    rewrite SameSide_DEF;
    fol B4';
  qed;
`;;

let DisjointOneNotOther = theorem `;
  ∀l m. (∀x:A. x ∈ m  ⇒ x ∉ l)  ⇔  l ∩ m = ∅
  by fol ∉ IN_INTER MEMBER_NOT_EMPTY`;;

let EquivIntersectionHelp = theorem `;
  ∀e x:A. ∀l m:A->bool.
  (l ∩ m = {x}  ∨  m ∩ l = {x})  ∧  e ∈ m ━ {x}   ⇒  e ∉ l
  by fol ∉ IN_INTER IN_SING IN_DIFF`;;

let CollinearSymmetry = theorem `;
  ∀A B C. Collinear A B C  ⇒
    Collinear A C B ∧ Collinear B A C ∧ Collinear B C A ∧
    Collinear C A B ∧ Collinear C B A

  proof
    intro_TAC ∀A B C, H1;
    consider l such that
    Line l ∧ A ∈ l ∧ B ∈ l ∧ C ∈ l     [l_line] by fol H1 Collinear_DEF;
    fol - Collinear_DEF;
  qed;
`;;

let ExistsNewPointOnLine = theorem `;
  ∀P. Line l ∧ P ∈ l  ⇒  ∃Q. Q ∈ l ∧ ¬(P = Q)

  proof
    intro_TAC ∀P, H1;
    consider A B such that
    A ∈ l ∧ B ∈ l ∧ ¬(A = B)     [l_line] by fol H1 I2;
    fol - l_line;
  qed;
`;;

let ExistsPointOffLine = theorem `;
  ∀l. Line l  ⇒  ∃Q. Q ∉ l

  proof
    intro_TAC ∀l, H1;
    consider A B C such that
    ¬(A = B) ∧ ¬(A = C) ∧ ¬(B = C) ∧ ¬Collinear A B C     [Distinct] by fol I3;
    assume (A ∈ l) ∧ (B ∈ l) ∧ (C ∈ l)     [all_on] by fol - ∉;
    Collinear A B C     [] by fol H1 - Collinear_DEF;
    fol - Distinct;
  qed;
`;;

let BetweenLinear = theorem `;
  ∀A B C m. Line m ∧ A ∈ m ∧ C ∈ m  ∧
    (B ∈ Open (A, C) ∨ C ∈ Open (B, A)  ∨ A ∈ Open (C, B))  ⇒  B ∈ m

  proof
    intro_TAC ∀A B C m, H1m H1A H1C H2;
    ¬(A = C) ∧
    (Collinear A B C ∨ Collinear B C A ∨ Collinear C A B)     [X1] by fol H2 B1';
    consider l such that
    Line l ∧ A ∈ l ∧ B ∈ l ∧ C ∈ l     [X2] by fol - Collinear_DEF;
    l = m     [] by fol X1 - H2 H1m H1A H1C I1;
    fol - X2;
  qed;
`;;

let CollinearLinear = theorem `;
  ∀A B C m. Line m ∧ A ∈ m ∧ C ∈ m  ∧
    (Collinear A B C ∨ Collinear B C A ∨ Collinear C A B)  ∧
    ¬(A = C)  ⇒  B ∈ m

  proof
    intro_TAC ∀A B C m, H1m H1A H1C H2 H3;
    consider l such that
    Line l ∧ A ∈ l ∧ B ∈ l ∧ C ∈ l     [X1] by fol H2 Collinear_DEF;
    l = m     [] by fol H3 - H1m H1A H1C I1;
    fol - X1;
  qed;
`;;

let NonCollinearImpliesDistinct = theorem `;
  ∀A B C. ¬Collinear A B C  ⇒  ¬(A = B) ∧ ¬(A = C) ∧ ¬(B = C)

  proof
    intro_TAC ∀A B C, H1;
    assume A = B ∧ B = C     [equal] by fol - H1 I1 Collinear_DEF;
    consider Q such that
    ¬(Q = A)     [notQA] by fol I3;
    fol - equal H1 I1 Collinear_DEF;
  qed;
`;;

let NonCollinearRaa = theorem `;
  ∀A B C l.  ¬(A = C)  ⇒  Line l ∧ A ∈ l ∧ C ∈ l  ⇒  B ∉ l
    ⇒  ¬Collinear A B C

  proof
    intro_TAC ∀A B C l, Distinct, l_line, notBl;
    assume Collinear A B C     [ANCcol] by fol -;
    consider m such that Line m ∧ A ∈ m ∧ B ∈ m ∧ C ∈ m     [m_line] by fol - Collinear_DEF;
    m = l     [] by fol - l_line Distinct I1;
    B ∈ l     [] by fol m_line -;
    fol - notBl ∉;
  qed;
`;;

let TwoSidesTriangle1Intersection = theorem `;
  ∀A B C Y. ¬Collinear A B C  ∧  Collinear B C Y  ∧  Collinear A C Y
     ⇒ Y = C

  proof
    intro_TAC ∀A B C Y, ABCcol BCYcol ACYcol;
    assume ¬(C = Y)     [notCY] by fol -;
    consider l such that
    Line l ∧ C ∈ l ∧ Y ∈ l     [l_line] by fol - I1;
    B ∈ l ∧ A ∈ l     [] by fol - BCYcol ACYcol Collinear_DEF notCY I1;
    fol - l_line Collinear_DEF ABCcol;
  qed;
`;;

let OriginInRay = theorem `;
  ∀O Q. ¬(Q = O)  ⇒  O ∈ ray O Q

  proof
    intro_TAC ∀O Q, H1;
    O ∉ Open (O, Q)     [OOQ] by fol B1' ∉;
    Collinear O Q O     [] by fol H1 I1 Collinear_DEF;
    fol H1 - OOQ IN_Ray;
  qed;
`;;

let EndpointInRay = theorem `;
  ∀O Q. ¬(Q = O)  ⇒  Q ∈ ray O Q

  proof
    intro_TAC ∀O Q, H1;
    O ∉ Open (Q, Q)     [notOQQ] by fol B1' ∉;
    Collinear O Q Q     [] by fol H1 I1 Collinear_DEF;
    fol H1 - notOQQ IN_Ray;
  qed;
`;;

let I1Uniqueness = theorem `;
  ∀X l m. Line l  ∧  Line m  ∧  ¬(l = m)  ∧  X ∈ l  ∧  X ∈ m
     ⇒ l ∩ m = {X}

  proof
    intro_TAC ∀X l m, H0l H0m H1 H2l H2m;
    assume ¬(l ∩ m = {X})     [H3] by fol -;
    consider A such that
    A ∈ l ∩ m  ∧ ¬(A = X)     [X1] by fol H2l H2m IN_INTER H3 EXTENSION IN_SING;
    fol H0l H0m H2l H2m IN_INTER X1 I1 H1;
  qed;
`;;

let DisjointLinesImplySameSide = theorem `;
  ∀l m A B.  Line l ∧ Line m ∧ A ∈ m ∧ B ∈ m ∧ l ∩ m = ∅  ⇒  A,B same_side l

  proof
    intro_TAC ∀l m A B, l_line m_line Am Bm lm0;
      l ∩ Open (A,B) = ∅     [] by fol Am Bm m_line BetweenLinear SUBSET lm0 SUBSET_REFL INTER_TENSOR SUBSET_EMPTY;
      fol l_line - SameSide_DEF SUBSET IN_INTER MEMBER_NOT_EMPTY;
  qed;
`;;

let EquivIntersection = theorem `;
  ∀A B X l m.  Line l ∧ Line m ∧ l ∩ m = {X} ∧ A ∈ m ━ {X} ∧ B ∈ m ━ {X} ∧
    X ∉ Open (A, B)  ⇒  A,B same_side l

  proof
    intro_TAC ∀A B X l m, l_line m_line H1 H2l H2m H3;
    Open (A, B) ⊂ m     [] by fol l_line m_line SUBSET_DIFF IN_DIFF IN_SING  H2l H2m BetweenLinear SUBSET;
    l ∩ Open (A, B) ⊂ {X}     [] by fol - H1 SUBSET_REFL INTER_TENSOR;
    l ∩ Open (A, B) ⊂ ∅     [] by fol - SUBSET IN_SING IN_INTER H3 ∉;
    fol l_line - SameSide_DEF SUBSET IN_INTER NOT_IN_EMPTY;
  qed;
`;;

let RayLine = theorem `;
  ∀O P l. Line l ∧ O ∈ l ∧ P ∈ l  ⇒  ray O P  ⊂ l
  by fol IN_Ray CollinearLinear SUBSET`;;

let RaySameSide = theorem `;
  ∀l O A P. Line l ∧ O ∈ l ∧ A ∉ l ∧ P ∈ ray O A ━ {O}
     ⇒  P ∉ l  ∧  P,A same_side l

  proof
    intro_TAC ∀l O A P, l_line Ol notAl PrOA;
    ¬(O = A)     [notOA] by fol l_line Ol notAl ∉;
    consider d such that
    Line d ∧ O ∈ d ∧ A ∈ d     [d_line] by fol notOA I1;
    ¬(l = d)     [] by fol - notAl ∉;
    l ∩ d = {O}     [ldO] by fol l_line Ol d_line - I1Uniqueness;
    A ∈ d ━ {O}     [Ad_O] by fol d_line notOA IN_DIFF IN_SING;
    ray O A ⊂ d     [] by fol d_line RayLine;
    P ∈ d ━ {O}     [Pd_O] by fol PrOA - SUBSET IN_DIFF IN_SING;
    P ∉ l     [notPl] by fol ldO - EquivIntersectionHelp;
    O ∉ Open (P, A)     [] by fol PrOA IN_DIFF IN_SING IN_Ray;
    P,A same_side l     [] by fol l_line Ol d_line ldO Ad_O Pd_O - EquivIntersection;
    fol notPl -;
  qed;
`;;

let IntervalRayEZ = theorem `;
  ∀A B C. B ∈ Open (A, C)  ⇒  B ∈ ray A C ━ {A}  ∧  C ∈ ray A B ━ {A}

  proof
    intro_TAC ∀A B C, H1;
    ¬(A = B) ∧ ¬(A = C) ∧ ¬(B = C) ∧ Collinear A B C     [ABC] by fol H1 B1';
    A ∉ Open (B, C)  ∧  A ∉ Open (C, B)     [] by fol - H1 B3' B1' ∉;
    fol ABC - CollinearSymmetry IN_Ray ∉ IN_DIFF IN_SING;
  qed;
`;;

let NoncollinearityExtendsToLine = theorem `;
  ∀A O B X. ¬Collinear A O B  ⇒  Collinear O B X  ∧ ¬(X = O)
      ⇒  ¬Collinear A O X

  proof
    intro_TAC ∀A O B X, H1, H2;
    ¬(A = O) ∧ ¬(A = B) ∧ ¬(O = B)     [Distinct] by fol H1 NonCollinearImpliesDistinct;
    consider b such that
    Line b ∧ O ∈ b ∧ B ∈ b     [b_line] by fol Distinct I1;
    A ∉ b     [notAb] by fol b_line H1 Collinear_DEF ∉;
    X ∈ b     [] by fol H2 b_line Distinct I1 Collinear_DEF;
    fol b_line - H2 notAb I1 Collinear_DEF ∉;
  qed;
`;;

let SameSideReflexive = theorem `;
  ∀l A. Line l ∧  A ∉ l ⇒ A,A same_side l
  by fol B1' SameSide_DEF`;;

let SameSideSymmetric = theorem `;
  ∀l A B. Line l ∧  A ∉ l ∧ B ∉ l ⇒
  A,B same_side l ⇒ B,A same_side l
  by fol SameSide_DEF B1'`;;

let SameSideTransitive = theorem `;
  ∀l A B C. Line l  ⇒  A ∉ l ∧ B ∉ l ∧ C ∉ l  ⇒  A,B same_side l
    ⇒  B,C same_side l  ⇒  A,C same_side l

  proof
    intro_TAC ∀l A B C, l_line, notABCl, Asim_lB, Bsim_lC;
    assume Collinear A B C  ∧ ¬(A = B) ∧ ¬(A = C) ∧ ¬(B = C)     [Distinct] by fol - l_line notABCl Asim_lB Bsim_lC B4'' SameSideReflexive;
    consider m such that
    Line m ∧ A ∈ m ∧ C ∈ m     [m_line] by fol Distinct I1;
    B ∈ m     [Bm] by fol - Distinct CollinearLinear;
    assume ¬(m ∩ l = ∅)     [Intersect] by fol - m_line l_line BetweenLinear SameSide_DEF IN_INTER NOT_IN_EMPTY;
    consider X such that
    X ∈ l ∧ X ∈ m     [Xlm] by fol - MEMBER_NOT_EMPTY IN_INTER;
    Collinear A X B  ∧  Collinear B A C  ∧  Collinear A B C     [ABXcol] by fol m_line Bm - Collinear_DEF;
    consider E such that
    E ∈ l ∧ ¬(E = X)     [El_X] by fol l_line Xlm ExistsNewPointOnLine;
    ¬Collinear E A X     [EAXncol] by fol l_line El_X Xlm notABCl I1 Collinear_DEF ∉;
    consider B' such that
    ¬(B = E)  ∧  B ∈ Open (E, B')     [EBB'] by fol notABCl El_X ∉ B2';
    ¬(B' = E) ∧ ¬(B' = B) ∧ Collinear B E B'     [EBB'col] by fol - B1' CollinearSymmetry;
    ¬Collinear A B B'  ∧  ¬Collinear B' B A  ∧  ¬Collinear B' A B     [ABB'ncol] by fol EAXncol ABXcol Distinct - NoncollinearityExtendsToLine CollinearSymmetry;
    ¬Collinear B' B C ∧  ¬Collinear B' A C ∧  ¬Collinear A B' C     [AB'Cncol] by fol ABB'ncol ABXcol Distinct NoncollinearityExtendsToLine CollinearSymmetry;
    B' ∈ ray E B ━ {E}  ∧  B ∈ ray E B' ━ {E}     [] by fol EBB' IntervalRayEZ;
    B' ∉ l  ∧  B',B same_side l  ∧  B,B' same_side l     [notB'l] by fol l_line El_X notABCl - RaySameSide;
    A,B' same_side l ∧  B',C same_side l     [] by fol l_line ABB'ncol notABCl notB'l Asim_lB - AB'Cncol Bsim_lC B4'';
    fol l_line AB'Cncol notABCl notB'l - B4'';
  qed;
`;;

let ConverseCrossbar = theorem `;
  ∀O A B G. ¬Collinear A O B  ∧  G ∈ Open (A, B)  ⇒  G ∈ int_angle A O B

  proof
    intro_TAC ∀O A B G, H1 H2;
    ¬(A = O) ∧ ¬(A = B) ∧ ¬(O = B)     [Distinct] by fol H1 NonCollinearImpliesDistinct;
    consider a such that
    Line a ∧ O ∈ a ∧ A ∈ a     [a_line] by fol - I1;
    consider b such that
    Line b ∧ O ∈ b ∧ B ∈ b     [b_line] by fol Distinct I1;
    consider l such that
    Line l ∧ A ∈ l ∧ B ∈ l     [l_line] by fol Distinct I1;
    B ∉ a  ∧  A ∉ b     [] by fol H1 a_line  b_line Collinear_DEF ∉;
    ¬(a = l)  ∧  ¬(b = l)     [] by fol - l_line ∉;
    a ∩ l = {A}  ∧  b ∩ l = {B}     [alA] by fol - a_line l_line b_line I1Uniqueness;
    ¬(A = G) ∧ ¬(A = B) ∧ ¬(G = B)     [AGB] by fol H2 B1';
    A ∉ Open (G, B)  ∧  B ∉ Open (G, A)     [notGAB] by fol H2 B3' B1' ∉;
    G ∈ l     [Gl] by fol l_line H2 BetweenLinear;
    G ∉ a  ∧  G ∉ b     [notGa] by fol alA Gl AGB IN_DIFF IN_SING EquivIntersectionHelp;
    G ∈ l ━ {A} ∧ B ∈ l ━ {A} ∧ G ∈ l ━ {B} ∧ A ∈ l ━ {B}      [] by fol Gl l_line AGB IN_DIFF IN_SING;
    G,B same_side a  ∧  G,A same_side b     [] by fol a_line l_line alA - notGAB b_line EquivIntersection;
    fol H1 a_line b_line notGa - IN_InteriorAngle;
  qed;
`;;

let InteriorUse = theorem `;
  ∀A O B P a b.
    Line a ∧ O ∈ a ∧ A ∈ a ∧ Line b ∧ O ∈ b ∧ B ∈ b  ⇒
    P  ∈ int_angle A O B  ⇒
    P ∉ a ∧ P ∉ b ∧ P,B same_side a ∧ P,A same_side b

  proof
    intro_TAC ∀A O B P a b, aOAbOB, P_AOB;
    consider α β such that ¬Collinear A O B ∧
    Line α ∧ O ∈ α ∧ A ∈ α ∧
    Line β ∧ O ∈ β ∧B ∈ β ∧
    P ∉ α ∧ P ∉ β ∧
    P,B same_side α ∧ P,A same_side β     [exists] by fol P_AOB IN_InteriorAngle;
    ¬(A = O) ∧ ¬(A = B) ∧ ¬(O = B)     [] by fol - NonCollinearImpliesDistinct;
    α = a ∧ β = b     [] by fol - aOAbOB exists I1;
    fol - exists;
  qed;
`;;

let InteriorEZHelp = theorem `;
  ∀A O B P. P ∈ int_angle A O B  ⇒
  ¬(P = A) ∧ ¬(P = O) ∧ ¬(P = B) ∧ ¬Collinear A O P

  proof
    intro_TAC ∀A O B P, P_AOB;
    consider a b such that
    ¬Collinear A O B ∧
    Line a ∧ O ∈ a ∧ A ∈ a ∧
    Line b ∧ O ∈ b ∧B ∈ b ∧
    P ∉ a ∧ P ∉ b     [def_int] by fol P_AOB IN_InteriorAngle;
    ¬(P = A) ∧ ¬(P = O) ∧ ¬(P = B)     [PnotAOB] by fol - ∉;
    ¬(A = O)     [] by fol def_int NonCollinearImpliesDistinct;
    ¬Collinear A O P     [] by fol def_int - NonCollinearRaa CollinearSymmetry;
    fol PnotAOB -;
  qed;
`;;

let InteriorAngleSymmetry = theorem `;
  ∀A O B P: point. P ∈ int_angle A O B  ⇒  P ∈ int_angle B O A

  proof     rewrite IN_InteriorAngle;     fol CollinearSymmetry;     qed;
`;;

let InteriorWellDefined = theorem `;
  ∀A O B X P. P ∈ int_angle A O B  ∧  X ∈ ray O B ━ {O}  ⇒  P ∈ int_angle A O X

  proof
    intro_TAC ∀A O B X P, H1 H2;
    consider a b such that
    ¬Collinear A O B ∧
    Line a ∧ O ∈ a ∧ A ∈ a ∧ P ∉ a     ∧     Line b ∧ O ∈ b ∧ B ∈ b ∧ P ∉ b ∧
    P,B same_side a ∧ P,A same_side b     [def_int] by fol H1 IN_InteriorAngle;
    ¬(X = O) ∧ ¬(O = B) ∧ Collinear O B X     [H2'] by fol H2 IN_Ray IN_DIFF IN_SING;
    B ∉ a     [notBa] by fol def_int Collinear_DEF ∉;
    ¬Collinear A O X     [AOXnoncol] by fol def_int H2' NoncollinearityExtendsToLine;
    X ∈ b     [Xb] by fol def_int H2' CollinearLinear;
    X ∉ a  ∧  B,X same_side a     [] by fol def_int notBa H2 RaySameSide SameSideSymmetric;
    P,X same_side a     [] by fol def_int - notBa SameSideTransitive;
    fol AOXnoncol def_int Xb - IN_InteriorAngle;
  qed;
`;;

let WholeRayInterior = theorem `;
  ∀A O B X P. X ∈ int_angle A O B  ∧  P ∈ ray O X ━ {O}  ⇒  P ∈ int_angle A O B

  proof
    intro_TAC ∀A O B X P, XintAOB PrOX;
    consider a b such that
    ¬Collinear A O B ∧
    Line a ∧ O ∈ a ∧ A ∈ a ∧ X ∉ a   ∧   Line b ∧ O ∈ b ∧ B ∈ b ∧ X ∉ b ∧
    X,B same_side a ∧ X,A same_side b     [def_int] by fol XintAOB IN_InteriorAngle;
    P ∉ a ∧ P,X same_side a ∧ P ∉ b ∧ P,X same_side b     [Psim_abX] by fol def_int PrOX RaySameSide;
    P,B same_side a  ∧ P,A same_side b     [] by fol - def_int Collinear_DEF SameSideTransitive ∉;
       fol def_int Psim_abX - IN_InteriorAngle;
  qed;
`;;

let AngleOrdering = theorem `;
  ∀O A P Q a. ¬(O = A)  ⇒  Line a ∧ O ∈ a ∧ A ∈ a  ⇒
    P ∉ a ∧ Q ∉ a  ⇒  P,Q same_side a  ⇒  ¬Collinear P O Q  ⇒
    P ∈ int_angle Q O A  ∨  Q ∈ int_angle P O A

  proof
    intro_TAC ∀O A P Q a, H1, H2, H3, H4, H5;
    ¬(P = O) ∧ ¬(P = Q) ∧ ¬(O = Q)     [Distinct] by fol H5 NonCollinearImpliesDistinct;
    consider q such that
    Line q ∧ O ∈ q ∧ Q ∈ q     [q_line] by fol Distinct I1;
    P ∉ q     [notPq] by fol - H5 Collinear_DEF ∉;
    assume ¬(P ∈ int_angle Q O A)     [notPintQOA] by fol -;
    ¬Collinear Q O A  ∧  ¬Collinear P O A     [POAncol] by fol H1 H2 H3 I1 Collinear_DEF ∉;
¬(P,A same_side q)     [] by fol - H2 q_line H3 notPq H4 notPintQOA IN_InteriorAngle;
    consider G such that
    G ∈ q ∧ G ∈ Open (P, A)     [existG] by fol q_line - SameSide_DEF;
    G ∈ int_angle P O A     [G_POA] by fol POAncol existG ConverseCrossbar;
    G ∉ a ∧ G,P same_side a ∧ ¬(G = O)     [Gsim_aP] by fol - H1 H2 IN_InteriorAngle I1 ∉;
    G,Q same_side a     [] by fol H2 Gsim_aP H3 H4 SameSideTransitive;
    O ∉ Open (Q, G)     [notQOG] by fol - H2 SameSide_DEF B1' ∉;
    Collinear O G Q     [] by fol q_line existG Collinear_DEF;
    Q ∈ ray O G ━ {O}     [] by fol Gsim_aP - notQOG Distinct IN_Ray IN_DIFF IN_SING;
    fol G_POA - WholeRayInterior;
  qed;
`;;

let InteriorsDisjointSupplement = theorem `;
  ∀A O B A'. ¬Collinear A O B  ∧  O ∈ Open (A, A')  ⇒
    int_angle B O A'  ∩  int_angle A O B = ∅

  proof
    intro_TAC ∀A O B A', H1 H2;
    ∀D. D ∈ int_angle A O B  ⇒  D ∉ int_angle B O A'     []
    proof
      intro_TAC ∀D, H3;
      ¬(A = O) ∧ ¬(O = B)     [] by fol H1 NonCollinearImpliesDistinct;
      consider a b such that
      Line a ∧ O ∈ a ∧ A ∈ a ∧ Line b ∧ O ∈ b ∧ B ∈ b ∧ A' ∈ a     [ab_line] by fol - H2 I1 BetweenLinear;
      ¬Collinear B O A'     [] by fol H1 H2 CollinearSymmetry B1' NoncollinearityExtendsToLine;
      A ∉ b  ∧  A' ∉ b     [notAb] by fol ab_line H1 - Collinear_DEF ∉;
      ¬(A',A same_side b)     [A'nsim_bA] by fol ab_line H2 B1' SameSide_DEF;
      D ∉ b  ∧  D,A same_side b     [DintAOB] by fol ab_line H3 InteriorUse;
      ¬(D,A' same_side b)     [] by fol ab_line notAb DintAOB A'nsim_bA SameSideSymmetric SameSideTransitive;
      fol ab_line - InteriorUse ∉;
    qed;
    fol - DisjointOneNotOther;
  qed;
`;;

let InteriorReflectionInterior = theorem `;
  ∀A O B D A'. O ∈ Open (A, A')  ∧  D ∈ int_angle A O B  ⇒
    B  ∈ int_angle D O A'

  proof
    intro_TAC ∀A O B D A', H1 H2;
    consider a b such that
    ¬Collinear A O B ∧ Line a ∧ O ∈ a ∧ A ∈ a ∧ D ∉ a ∧
    Line b ∧ O ∈ b ∧ B ∈ b ∧ D ∉ b ∧ D,B same_side a     [DintAOB] by fol H2 IN_InteriorAngle;
    ¬(O = B) ∧ ¬(O = A') ∧ B ∉ a     [Distinct] by fol - H1 NonCollinearImpliesDistinct B1' Collinear_DEF ∉;
    ¬Collinear D O B     [DOB_ncol] by fol DintAOB - NonCollinearRaa CollinearSymmetry;
    A' ∈ a     [A'a] by fol H1 DintAOB BetweenLinear;
    D ∉ int_angle B O A'     [] by fol DintAOB H1 H2 InteriorsDisjointSupplement DisjointOneNotOther;
    fol Distinct DintAOB A'a DOB_ncol - AngleOrdering ∉;
  qed;
`;;

let Crossbar_THM = theorem `;
  ∀O A B D. D ∈ int_angle A O B  ⇒  ∃G. G ∈ Open (A, B)  ∧  G ∈ ray O D ━ {O}

  proof
    intro_TAC ∀O A B D, H1;
    consider a b such that
    ¬Collinear A O B ∧
    Line a ∧ O ∈ a ∧ A ∈ a ∧
    Line b ∧ O ∈ b ∧ B ∈ b ∧
    D ∉ a ∧ D ∉ b ∧ D,B same_side a ∧ D,A same_side b     [DintAOB] by fol H1 IN_InteriorAngle;
    B ∉ a     [notBa] by fol DintAOB Collinear_DEF ∉;
    ¬(A = O) ∧ ¬(A = B) ∧ ¬(O = B) ∧ ¬(D = O)     [Distinct] by fol DintAOB NonCollinearImpliesDistinct ∉;
    consider l such that
    Line l ∧ O ∈ l ∧ D ∈ l     [l_line] by fol - I1;
    consider A' such that
    O ∈ Open (A, A')     [AOA'] by fol Distinct B2';
    A' ∈ a ∧ Collinear A O A' ∧ ¬(A' = O)      [A'a] by fol DintAOB - BetweenLinear B1';
    ¬(A,A' same_side l)     [Ansim_lA'] by fol l_line AOA' SameSide_DEF;
    B ∈ int_angle D O A'     [] by fol H1 AOA' InteriorReflectionInterior;
    B,A' same_side l     [Bsim_lA'] by fol l_line DintAOB A'a - InteriorUse;
    ¬Collinear A O D  ∧  ¬Collinear B O D      [AODncol] by fol H1 InteriorEZHelp InteriorAngleSymmetry;
    ¬Collinear D O A'      [] by fol - A'a CollinearSymmetry NoncollinearityExtendsToLine;
    A ∉ l ∧ B ∉ l ∧ A' ∉ l     [] by fol l_line AODncol - Collinear_DEF ∉;
    ¬(A,B same_side l)     [] by fol l_line - Bsim_lA' Ansim_lA' SameSideTransitive;
    consider G such that
    G ∈ Open (A, B) ∧ G ∈ l     [AGB] by fol l_line - SameSide_DEF;
    Collinear O D G     [ODGcol] by fol - l_line Collinear_DEF;
    G ∈ int_angle A O B     [] by fol DintAOB AGB ConverseCrossbar;
    G ∉ a  ∧  G,B same_side a  ∧  ¬(G = O)     [Gsim_aB] by fol DintAOB - InteriorUse ∉;
    B,D same_side a     [] by fol DintAOB notBa SameSideSymmetric;
    G,D same_side a     [Gsim_aD] by fol DintAOB Gsim_aB notBa - SameSideTransitive;
    O ∉ Open (G, D)     [] by fol DintAOB - SameSide_DEF ∉;
    G ∈ ray O D ━ {O}     [] by fol Distinct ODGcol - Gsim_aB IN_Ray IN_DIFF IN_SING;
    fol AGB -;
  qed;
`;;

let AlternateConverseCrossbar = theorem `;
  ∀O A B G. Collinear A G B  ∧  G ∈ int_angle A O B  ⇒  G ∈ Open (A, B)

  proof
    intro_TAC ∀O A B G, H1;
    consider a b such that
    ¬Collinear A O B  ∧  Line a ∧ O ∈ a ∧ A ∈ a  ∧  Line b ∧ O ∈ b ∧ B ∈ b  ∧
    G,B same_side a  ∧  G,A same_side b     [GintAOB] by fol H1 IN_InteriorAngle;
    ¬(A = B) ∧ ¬(G = A) ∧ ¬(G = B)  ∧  A ∉ Open (G, B)  ∧  B ∉ Open (G, A)     [] by fol - H1 NonCollinearImpliesDistinct InteriorEZHelp SameSide_DEF ∉;
    fol - H1 B1' B3' ∉;
  qed;
`;;

let InteriorOpposite = theorem `;
  ∀A O B P p. P ∈ int_angle A O B  ⇒  Line p ∧ O ∈ p ∧ P ∈ p
    ⇒  ¬(A,B same_side p)

  proof
    intro_TAC ∀A O B P p, PintAOB, p_line;
    consider G such that
    G ∈ Open (A, B) ∧ G ∈ ray O P     [Gexists] by fol PintAOB Crossbar_THM IN_DIFF;
    fol p_line p_line - RayLine SUBSET Gexists SameSide_DEF;
  qed;
`;;

let IntervalTransitivity = theorem `;
  ∀O P Q R m. Line m  ∧ O ∈ m  ⇒  P ∈ m ━ {O} ∧ Q ∈ m ━ {O} ∧ R ∈ m ━ {O}  ⇒
    O ∉ Open (P, Q) ∧ O ∉ Open (Q, R)  ⇒  O ∉ Open (P, R)

  proof
    intro_TAC ∀O P Q R m, H0, H2, H3;
    consider E such that
    E ∉ m ∧  ¬(O = E)     [notEm] by fol H0 ExistsPointOffLine ∉;
    consider l such that
    Line l ∧ O ∈ l ∧ E ∈ l     [l_line] by fol - I1;
    ¬(m = l)     [] by fol notEm - ∉;
    l ∩ m = {O}     [lmO] by fol l_line H0 - l_line I1Uniqueness;
    P ∉ l ∧  Q ∉ l ∧ R ∉ l     [notPQRl] by fol - H2 EquivIntersectionHelp;
    P,Q same_side l  ∧  Q,R same_side l     [] by fol l_line H0 lmO H2 H3 EquivIntersection;
    P,R same_side l     [Psim_lR] by fol l_line notPQRl - SameSideTransitive;
    fol l_line - SameSide_DEF ∉;
  qed;
`;;

let RayWellDefinedHalfway = theorem `;
  ∀O P Q. ¬(Q = O)  ∧  P ∈ ray O Q ━ {O}  ⇒  ray O P ⊂ ray O Q

  proof
    intro_TAC ∀O P Q, H1 H2;
    consider m such that
    Line m ∧ O ∈ m ∧ Q ∈ m     [OQm] by fol H1 I1;
    P ∈ ray O Q  ∧  ¬(P = O)  ∧  O ∉ Open (P, Q)     [H2'] by fol H2 IN_Ray IN_DIFF IN_SING;
    P ∈ m  ∧  P ∈ m ━ {O}  ∧  Q ∈ m ━ {O}     [PQm_O] by fol OQm H2' RayLine SUBSET H2' OQm H1 IN_DIFF IN_SING;
    O ∉ Open (P, Q)     [notPOQ] by fol H2' IN_Ray;
    rewrite SUBSET;
    X_genl_TAC X;    intro_TAC XrayOP;
    X ∈ m  ∧  O ∉ Open (X, P)     [XrOP] by fol - SUBSET OQm PQm_O H2' RayLine IN_Ray;
    Collinear O Q X     [OQXcol] by fol OQm -  Collinear_DEF;
    assume ¬(X = O)     [notXO] by fol H1 - OriginInRay;
    X ∈ m ━ {O}     [] by fol XrOP - IN_DIFF IN_SING;
    O ∉ Open (X, Q)     [] by fol OQm - PQm_O XrOP H2' IntervalTransitivity;
    fol H1 OQXcol - IN_Ray;
  qed;
`;;

let RayWellDefined = theorem `;
  ∀O P Q. ¬(Q = O)  ∧  P ∈ ray O Q ━ {O}  ⇒  ray O P = ray O Q

  proof
    intro_TAC ∀O P Q, H1  H2;
    ray O P ⊂ ray O Q     [PsubsetQ] by fol H1 H2 RayWellDefinedHalfway;
    ¬(P = O)  ∧  Collinear O Q P  ∧  O ∉ Open (P, Q)     [H2'] by fol H2 IN_Ray IN_DIFF IN_SING;
    Q ∈ ray O P ━ {O}     [] by fol H2' B1' ∉ CollinearSymmetry IN_Ray H1 IN_DIFF IN_SING;
    ray O Q ⊂ ray O P     [QsubsetP] by fol H2' - RayWellDefinedHalfway;
    fol PsubsetQ QsubsetP SUBSET_ANTISYM;
  qed;
`;;

let OppositeRaysIntersect1pointHelp = theorem `;
  ∀A O B X. O ∈ Open (A, B)  ∧  X ∈ ray O B ━ {O}
    ⇒  X ∉ ray O A  ∧  O ∈ Open (X, A)

  proof
    intro_TAC ∀A O B X, H1 H2;
    ¬(A = O) ∧ ¬(A = B) ∧ ¬(O = B) ∧ Collinear A O B     [AOB] by fol H1 B1';
    ¬(X = O) ∧ Collinear O B X ∧ O ∉ Open (X, B)     [H2'] by fol H2 IN_Ray IN_DIFF IN_SING;
    consider m such that
    Line m ∧ A ∈ m ∧ B ∈ m     [m_line] by fol AOB I1;
    O ∈ m  ∧ X ∈ m     [Om] by fol m_line H2' AOB CollinearLinear;
    A ∈ m ━ {O}  ∧  X ∈ m ━ {O}  ∧  B ∈ m ━ {O}     [] by fol m_line - H2' AOB IN_DIFF IN_SING;
    fol H1 m_line Om - H2' IntervalTransitivity ∉ B1' IN_Ray;
  qed;
`;;

let OppositeRaysIntersect1point = theorem `;
  ∀A O B. O ∈ Open (A, B)  ⇒  ray O A ∩ ray O B  =  {O}

  proof
    intro_TAC ∀A O B, H1;
    ¬(A = O) ∧ ¬(O = B)     [] by fol H1 B1';
    rewrite GSYM SUBSET_ANTISYM_EQ SUBSET IN_INTER;
    conj_tac     [Right] by fol - OriginInRay IN_SING;
    fol H1 OppositeRaysIntersect1pointHelp IN_DIFF IN_SING ∉;
  qed;
`;;

let IntervalRay = theorem `;
  ∀A B C. B ∈ Open (A, C)  ⇒  ray A B = ray A C
  by fol B1' IntervalRayEZ RayWellDefined`;;

let Reverse4Order = theorem `;
  ∀A B C D. ordered A B C D  ⇒  ordered D C B A
  proof
    rewrite Ordered_DEF;
    fol B1';
  qed;
`;;

let TransitivityBetweennessHelp = theorem `;
  ∀A B C D. B ∈ Open (A, C)  ∧  C ∈ Open (B, D)
   ⇒  B ∈ Open (A, D)

  proof
    intro_TAC ∀A B C D, H1;
    D ∈ ray B C ━ {B}     [] by fol H1 IntervalRayEZ;
    fol H1 - OppositeRaysIntersect1pointHelp B1';
  qed;
`;;

let TransitivityBetweenness = theorem `;
  ∀A B C D. B ∈ Open (A, C)  ∧  C ∈ Open (B, D)  ⇒  ordered A B C D

  proof
    intro_TAC ∀A B C D, H1;
    B ∈ Open (A, D)     [ABD] by fol H1 TransitivityBetweennessHelp;
    C ∈ Open (D, B)  ∧  B ∈ Open (C, A)     [] by fol H1 B1';
    C ∈ Open (D, A)     [] by fol - TransitivityBetweennessHelp;
    fol H1 ABD - B1' Ordered_DEF;
  qed;
`;;

let IntervalsAreConvex = theorem `;
  ∀A B C. B ∈ Open (A, C)  ⇒  Open (A, B)  ⊂  Open (A, C)

  proof
    intro_TAC ∀A B C, H1;
    ∀X. X ∈ Open (A, B)  ⇒  X ∈ Open (A, C)     []
    proof
      intro_TAC ∀X, AXB;
      X ∈ ray B A ━ {B}     [] by fol AXB B1' IntervalRayEZ;
      B ∈ Open (X, C)     [] by fol H1 B1' - OppositeRaysIntersect1pointHelp;
      fol AXB - TransitivityBetweennessHelp;
    qed;
    fol - SUBSET;
  qed;
`;;

let TransitivityBetweennessVariant = theorem `;
  ∀A X B C. X ∈ Open (A, B)  ∧  B ∈ Open (A, C)  ⇒  ordered A X B C

  proof
    intro_TAC ∀A X B C, H1;
    X ∈ ray B A ━ {B}     [] by fol H1 B1' IntervalRayEZ;
    B ∈ Open (X, C)     [] by fol H1 B1' - OppositeRaysIntersect1pointHelp;
    fol H1 - TransitivityBetweenness;
  qed;
`;;

let Interval2sides2aLineHelp = theorem `;
  ∀A B C X. B ∈ Open (A, C)  ⇒  X ∉ Open (A, B) ∨ X ∉ Open (B, C)

  proof
    intro_TAC ∀A B C X, H1;
    assume ¬(X ∉ Open (A, B))     [AXB] by fol -;
    ordered A X B C     [] by fol - ∉ H1 TransitivityBetweennessVariant;
    fol MESON [-; Ordered_DEF] [B ∈ Open (X, C)] B1' B3' ∉;
  qed;
`;;

let Interval2sides2aLine = theorem `;
  ∀A B C X. Collinear A B C
    ⇒  X ∉ Open (A, B)  ∨  X ∉ Open (A, C)  ∨  X ∉ Open (B, C)

  proof
    intro_TAC ∀A B C X, H1;
    assume ¬(A = B) ∧ ¬(A = C) ∧ ¬(B = C)     [Distinct] by fol - B1' ∉;
    B ∈ Open (A, C)  ∨  C ∈ Open (B, A)  ∨  A ∈ Open (C, B)     [] by fol - H1 B3';
    fol - Interval2sides2aLineHelp B1' ∉;
  qed;
`;;

let TwosidesTriangle2aLine = theorem `;
  ∀A B C l. Line l ∧ ¬Collinear A B C  ⇒  A ∉ l ∧ B ∉ l ∧ C ∉ l  ⇒
    ¬(A,B same_side l) ∧ ¬(B,C same_side l)  ⇒  A,C same_side l

  proof
    intro_TAC ∀ A B C l, H1, off_l, H2;
    ¬(A = B) ∧ ¬(A = C) ∧ ¬(B = C)     [ABCdistinct] by fol H1 NonCollinearImpliesDistinct;
    consider m such that
    Line m ∧ A ∈ m ∧ C ∈ m     [m_line] by fol - I1;
    assume ¬(l ∩ m = ∅)     [lmIntersect] by fol H1 m_line - DisjointLinesImplySameSide;
    consider Y such that
    Y ∈ l ∧ Y ∈ m     [Ylm] by fol lmIntersect MEMBER_NOT_EMPTY IN_INTER;
    consider X Z such that
    X ∈ l  ∧  X ∈ Open (A, B)  ∧  Z ∈ l  ∧  Z ∈ Open (C, B)     [H2'] by fol H1 H2 SameSide_DEF B1';
    ¬(A = B) ∧ ¬(A = C) ∧ ¬(B = C) ∧ Y ∈ m ━ {A}  ∧  Y ∈ m ━ {C}  ∧  C ∈ m ━ {A}  ∧  A ∈ m ━ {C}     [Distinct] by fol H1 NonCollinearImpliesDistinct Ylm off_l ∉ m_line IN_DIFF IN_SING;
    consider p such that
    Line p ∧ B ∈ p ∧ A ∈ p     [p_line] by fol Distinct I1;
    consider q such that
    Line q ∧ B ∈ q ∧ C ∈ q     [q_line] by fol Distinct I1;
    X ∈ p  ∧ Z ∈ q     [Xp] by fol p_line H2' BetweenLinear q_line H2';
    A ∉ q ∧ B ∉ m ∧ C ∉ p     [vertex_off_line] by fol q_line m_line p_line H1 Collinear_DEF ∉;
    X ∉ q  ∧  X,A same_side q  ∧  Z ∉ p  ∧  Z,C same_side p     [Xsim_qA] by fol q_line p_line - H2' B1' IntervalRayEZ RaySameSide;
    ¬(m = p)  ∧  ¬(m = q)     [] by fol m_line vertex_off_line ∉;
    p ∩ m = {A}  ∧  q ∩ m = {C}     [pmA] by fol p_line m_line q_line H1 - Xp H2' I1Uniqueness;
    Y ∉ p  ∧  Y ∉ q     [notYpq] by fol - Distinct EquivIntersectionHelp;
    X ∈ ray A B ━ {A}  ∧  Z ∈ ray C B ━ {C}     [] by fol H2' IntervalRayEZ H2' B1';
    X ∉ m  ∧  Z ∉ m  ∧  X,B same_side m  ∧  B,Z same_side m     [notXZm] by fol m_line vertex_off_line - RaySameSide SameSideSymmetric;
    X,Z same_side m     [] by fol m_line - vertex_off_line SameSideTransitive;
    Collinear X Y Z ∧ Y ∉ Open (X, Z) ∧  ¬(Y = X) ∧ ¬(Y = Z) ∧ ¬(X = Z)     [] by fol H1 H2' Ylm Collinear_DEF m_line - SameSide_DEF notXZm Xsim_qA Xp ∉;
    Z ∈ Open (X, Y)  ∨  X ∈ Open (Z, Y)     [] by fol - B3' ∉ B1';
    case_split ZXY | XZY     by fol -;
    suppose X ∈ Open (Z, Y);
      ¬(Z,Y same_side p)     [] by fol p_line Xp - SameSide_DEF;
      ¬(C,Y same_side p)     [] by fol p_line Xsim_qA vertex_off_line notYpq - SameSideTransitive;
      A ∈ Open (C, Y)     [] by fol p_line m_line pmA Distinct - EquivIntersection ∉;
      fol H1 Ylm off_l - B1' IntervalRayEZ RaySameSide;
    end;
    suppose Z ∈ Open (X, Y);
      ¬(X,Y same_side q)     [] by fol q_line Xp - SameSide_DEF;
      ¬(A,Y same_side q)     [] by fol q_line Xsim_qA vertex_off_line notYpq - SameSideTransitive;
      C ∈ Open (Y, A)     [] by fol q_line m_line pmA Distinct - EquivIntersection ∉ B1';
      fol H1 Ylm off_l - IntervalRayEZ RaySameSide;
    end;
  qed;
`;;

let LineUnionOf2Rays = theorem `;
  ∀A O B l. Line l ∧ A ∈ l ∧ B ∈ l  ⇒  O ∈ Open (A, B)
   ⇒  l = ray O A ∪ ray O B

  proof
    intro_TAC ∀A O B l, H1, H2;
    ¬(A = O) ∧ ¬(O = B) ∧ O ∈ l     [Distinct] by fol H2 B1' H1 BetweenLinear;
    ray O A ∪ ray O B  ⊂  l     [AOBsub_l] by fol H1 - RayLine UNION_SUBSET;
    ∀X. X ∈ l  ⇒  X ∈ ray O A  ∨  X ∈ ray O B     []
    proof
      intro_TAC ∀X, Xl;
      assume ¬(X ∈ ray O B)     [notXrOB] by fol -;
      Collinear O B X  ∧  Collinear X A B  ∧  Collinear O A X     [XABcol] by fol Distinct H1 Xl Collinear_DEF;
      O ∈ Open (X, B)     [] by fol notXrOB Distinct - IN_Ray ∉;
      O ∉ Open (X, A)     [] by fol ∉ B1' XABcol - H2 Interval2sides2aLine;
      fol Distinct XABcol - IN_Ray;
    qed;
    l ⊂ ray O A ∪ ray O B     [] by fol - IN_UNION SUBSET;
    fol - AOBsub_l SUBSET_ANTISYM;
  qed;
`;;

let AtMost2Sides = theorem `;
  ∀A B C l.  Line l  ⇒  A ∉ l ∧ B ∉ l ∧ C ∉ l
   ⇒  A,B same_side l  ∨  A,C same_side l  ∨  B,C same_side l

  proof
    intro_TAC ∀A B C l, l_line, H2;
    assume ¬(A = C)     [notAC] by fol - l_line H2 SameSideReflexive;
    assume Collinear A B C     [ABCcol] by fol - l_line H2 TwosidesTriangle2aLine;
    consider m such that
    Line m ∧ A ∈ m ∧ B ∈ m ∧ C ∈ m     [m_line] by fol notAC - I1 Collinear_DEF;
    assume ¬(m ∩ l = ∅)     [m_lNot0] by fol m_line l_line - BetweenLinear SameSide_DEF IN_INTER NOT_IN_EMPTY;
    consider X such that
    X ∈ l ∧ X ∈ m     [Xlm] by fol - IN_INTER MEMBER_NOT_EMPTY;
    A ∈ m ━ {X}  ∧  B ∈ m ━ {X}  ∧  C ∈ m ━ {X}     [ABCm_X] by fol m_line - H2 ∉ IN_DIFF IN_SING;
    X ∉ Open (A, B)  ∨  X ∉ Open (A, C)  ∨  X ∉ Open (B, C)     [] by fol ABCcol Interval2sides2aLine;
    fol l_line m_line m_line Xlm H2 ∉ I1Uniqueness ABCm_X - EquivIntersection;
  qed;
`;;

let FourPointsOrder = theorem `;
  ∀A B C X l.  Line l ∧ A ∈ l ∧ B ∈ l ∧ C ∈ l ∧ X ∈ l  ⇒
    ¬(X = A) ∧ ¬(X = B) ∧ ¬(X = C)  ⇒  B ∈ Open (A, C)
   ⇒  ordered X A B C  ∨  ordered A X B C  ∨
       ordered A B X C  ∨  ordered A B C X

  proof
    intro_TAC ∀A B C X l, H1, H2, H3;
    A ∈ Open (X, B)  ∨  X ∈ Open (A, B)  ∨  X ∈ Open (B, C)  ∨  C ∈ Open (B, X)     []
    proof
      ¬(A = B) ∧ ¬(B = C)     [ABCdistinct] by fol H3 B1';
      Collinear A B X ∧ Collinear A C X ∧ Collinear C B X     [ACXcol] by fol H1 Collinear_DEF;
      A ∈ Open (X, B)  ∨  X ∈ Open (A, B)  ∨  B ∈ Open (A, X)     [3pos] by fol H2 ABCdistinct - B3' B1';
      assume B ∈ Open (A, X)     [ABX]     by fol 3pos -;
      B ∉ Open (C, X)     [] by fol ACXcol H3 - Interval2sides2aLine ∉;
      fol H2 ABCdistinct ACXcol - B3' B1' ∉;
    qed;
    fol - H3 B1' TransitivityBetweenness TransitivityBetweennessVariant Reverse4Order;
  qed;
`;;

let HilbertAxiomRedundantByMoore = theorem `;
  ∀A B C D l.  Line l ∧ A ∈ l ∧ B ∈ l ∧ C ∈ l ∧ D ∈ l  ⇒
    ¬(A = B) ∧ ¬(A = C) ∧ ¬(A = D) ∧ ¬(B = C) ∧ ¬(B = D) ∧ ¬(C = D)
   ⇒  ordered D A B C ∨ ordered A D B C ∨ ordered A B D C ∨ ordered A B C D ∨
       ordered D A C B ∨ ordered A D C B ∨ ordered A C D B ∨ ordered A C B D ∨
       ordered D C A B ∨ ordered C D A B ∨ ordered C A D B ∨ ordered C A B D

  proof
    intro_TAC ∀A B C D l, H1, H2;
    Collinear A B C     [] by fol H1 Collinear_DEF;
    B ∈ Open (A, C)  ∨  C ∈ Open (A, B)  ∨  A ∈ Open (C, B)     [] by fol H2 - B3' B1';
    fol - H1 H2 FourPointsOrder;
  qed;
`;;

let InteriorTransitivity = theorem `;
  ∀A O B M G.  G ∈ int_angle A O B  ∧  M ∈ int_angle A O G
   ⇒  M ∈ int_angle A O B

  proof
    intro_TAC ∀A O B M G, GintAOB MintAOG;
    ¬Collinear A O B     [AOBncol] by fol GintAOB IN_InteriorAngle;
    consider G' such that
    G' ∈ Open (A, B)  ∧  G' ∈ ray O G ━ {O}     [CrossG] by fol GintAOB Crossbar_THM;
    M ∈ int_angle A O G'     [] by fol MintAOG - InteriorWellDefined;
    consider M' such that
    M' ∈ Open (A, G')  ∧  M' ∈ ray O M ━ {O}     [CrossM] by fol - Crossbar_THM;
    ¬(M' = O) ∧ ¬(M = O) ∧ Collinear O M M' ∧ O ∉ Open (M', M)     [] by fol - IN_Ray IN_DIFF IN_SING;
    M ∈ ray O M' ━ {O}     [MrOM'] by fol - CollinearSymmetry B1' ∉ IN_Ray IN_DIFF IN_SING;
    Open (A, G') ⊂ Open (A, B)  ∧  M' ∈ Open (A, B)     [] by fol CrossG IntervalsAreConvex CrossM SUBSET;
    M' ∈ int_angle A O B     [] by fol AOBncol - ConverseCrossbar;
    fol - MrOM' WholeRayInterior;
  qed;
`;;

let HalfPlaneConvexNonempty = theorem `;
  ∀l H A.  Line l ∧ A ∉ l  ⇒  H = {X | X ∉ l  ∧  X,A same_side l}
    ⇒  ¬(H = ∅)  ∧  H ⊂ complement l  ∧  Convex H

  proof
    intro_TAC ∀l H A, l_line, HalfPlane;
    ∀X. X ∈ H  ⇔  X ∉ l  ∧  X,A same_side l     [Hdef] by simplify HalfPlane IN_ELIM_THM;
    H ⊂ complement l     [Hsub] by fol - IN_PlaneComplement SUBSET;
    A,A same_side l  ∧  A ∈ H     [] by fol l_line SameSideReflexive Hdef;
    ¬(H = ∅)     [Hnonempty] by fol - MEMBER_NOT_EMPTY;
    ∀P Q X.  P ∈ H ∧ Q ∈ H ∧ X ∈ Open (P, Q)  ⇒  X ∈ H     []
    proof
      intro_TAC ∀P Q X, PXQ;
      P ∉ l  ∧  P,A same_side l  ∧  Q ∉ l  ∧  Q,A same_side l     [PQinH] by fol - Hdef;
      P,Q same_side l     [Psim_lQ] by fol l_line - SameSideSymmetric SameSideTransitive;
      X ∉ l     [notXl] by fol - PXQ SameSide_DEF ∉;
      Open (X, P) ⊂ Open (P, Q)     [] by fol PXQ IntervalsAreConvex B1' SUBSET;
      X,P same_side l     [] by fol l_line - SUBSET Psim_lQ SameSide_DEF;
      X,A same_side l     [] by fol l_line notXl PQinH - Psim_lQ PQinH SameSideTransitive;
      fol - notXl Hdef;
    qed;
    fol Hnonempty Hsub - SUBSET CONVEX;
  qed;
`;;

let PlaneSeparation = theorem `;
  ∀l.  Line l
   ⇒  ∃H1 H2. H1 ∩ H2 = ∅  ∧  ¬(H1 = ∅)  ∧  ¬(H2 = ∅)  ∧
         Convex H1  ∧  Convex H2  ∧  complement l = H1 ∪ H2  ∧
         ∀P Q. P ∈ H1 ∧ Q ∈ H2  ⇒  ¬(P,Q same_side l)

  proof
    intro_TAC ∀l, l_line;
    consider A such that
    A ∉ l     [notAl] by fol l_line ExistsPointOffLine;
    consider E such that
    E ∈ l  ∧  ¬(A = E)     [El] by fol l_line I2 - ∉;
    consider B such that
    E ∈ Open (A, B)  ∧  ¬(E = B)  ∧  Collinear A E B     [AEB] by fol - B2' B1';
    B ∉ l     [notBl] by fol - l_line El ∉ notAl NonCollinearRaa CollinearSymmetry;
    ¬(A,B same_side l)     [Ansim_lB] by fol l_line El AEB SameSide_DEF;
    consider H1 H2 such that
    H1 = {X | X ∉ l  ∧  X,A same_side l}  ∧
    H2 = {X | X ∉ l  ∧  X,B same_side l}     [H12sets] by fol;
    ∀X. (X ∈ H1  ⇔  X ∉ l ∧ X,A same_side l) ∧
         (X ∈ H2  ⇔  X ∉ l ∧ X,B same_side l)     [H12def] by simplify IN_ELIM_THM -;
    H1 ∩ H2 = ∅     [H12disjoint]
    proof
      assume ¬(H1 ∩ H2 = ∅)     [nonempty] by fol -;
      consider V such that
      V ∈ H1 ∧ V ∈ H2     [VinH12] by fol - MEMBER_NOT_EMPTY IN_INTER;
      V ∉ l  ∧  V,A same_side l  ∧  V ∉ l  ∧  V,B same_side l     [] by fol - H12def;
      A,B same_side l     [] by fol l_line - notAl notBl SameSideSymmetric SameSideTransitive;
      fol - Ansim_lB;
    qed;
    ¬(H1 = ∅) ∧ ¬(H2 = ∅) ∧ H1 ⊂ complement l ∧ H2 ⊂ complement l ∧
    Convex H1 ∧ Convex H2     [H12convex_nonempty] by fol l_line notAl notBl H12sets HalfPlaneConvexNonempty;
    H1 ∪ H2  ⊂  complement l     [H12sub] by fol H12convex_nonempty UNION_SUBSET;
    ∀C. C ∈ complement l  ⇒  C ∈ H1 ∪ H2     []
    proof
      intro_TAC ∀C, compl;
      C ∉ l     [notCl] by fol - IN_PlaneComplement;
      C,A same_side l  ∨  C,B same_side l     [] by fol l_line notAl notBl - Ansim_lB AtMost2Sides;
      fol notCl - H12def IN_UNION;
    qed;
    complement l  ⊂  H1 ∪ H2     [] by fol - SUBSET;
    complement l  =  H1 ∪ H2     [compl_H1unionH2] by fol H12sub - SUBSET_ANTISYM;
    ∀P Q. P ∈ H1 ∧ Q ∈ H2  ⇒  ¬(P,Q same_side l)     [opp_sides]
    proof
      intro_TAC ∀P Q, both;
      P ∉ l  ∧  P,A same_side l  ∧   Q ∉ l  ∧  Q,B same_side l     [PH1_QH2] by fol - H12def IN;
      fol l_line - notAl SameSideSymmetric notBl Ansim_lB SameSideTransitive;
    qed;
    fol H12disjoint H12convex_nonempty compl_H1unionH2 opp_sides;
  qed;
`;;

let TetralateralSymmetry = theorem `;
  ∀A B C D.  Tetralateral A B C D
    ⇒  Tetralateral B C D A ∧ Tetralateral A B D C

  proof
    intro_TAC ∀A B C D, H1;
    ¬Collinear A B D ∧ ¬Collinear B D C ∧ ¬Collinear D C A ∧ ¬Collinear C A B      [TetraABCD] by fol H1 Tetralateral_DEF CollinearSymmetry;
    simplify H1 - Tetralateral_DEF;
    fol H1 Tetralateral_DEF;
  qed;
`;;

let EasyEmptyIntersectionsTetralateralHelp = theorem `;
  ∀A B C D. Tetralateral A B C D  ⇒  Open (A, B) ∩ Open (B, C) = ∅

  proof
    intro_TAC ∀A B C D, H1;
    ∀X. X ∈ Open (B, C)  ⇒  X ∉ Open (A, B)     []
    proof
      intro_TAC ∀X, BXC;
      ¬Collinear A B C ∧ Collinear B X C ∧ ¬(X = B)     [] by fol H1 Tetralateral_DEF - B1';
      ¬Collinear A X B     [] by fol - CollinearSymmetry B1' NoncollinearityExtendsToLine;
      fol - B1' ∉;
    qed;
    fol - DisjointOneNotOther;
  qed;
`;;

let EasyEmptyIntersectionsTetralateral = theorem `;
  ∀A B C D. Tetralateral A B C D
   ⇒  Open (A, B) ∩ Open (B, C) = ∅  ∧  Open (B, C) ∩ Open (C, D) = ∅  ∧
       Open (C, D) ∩ Open (D, A) = ∅  ∧  Open (D, A) ∩ Open (A, B) = ∅

  proof
    intro_TAC ∀A B C D, H1;
    Tetralateral B C D A  ∧ Tetralateral C D A B  ∧ Tetralateral D A B C     [] by fol H1 TetralateralSymmetry;
    fol H1 - EasyEmptyIntersectionsTetralateralHelp;
  qed;
`;;

let SegmentSameSideOppositeLine = theorem `;
  ∀A B C D a c.  Quadrilateral A B C D  ⇒
    Line a ∧ A ∈ a ∧ B ∈ a  ⇒  Line c ∧ C ∈ c ∧ D ∈ c
    ⇒  A,B same_side c  ∨  C,D same_side a

  proof
    intro_TAC ∀A B C D a c, H1, a_line, c_line;
    assume ¬(C,D same_side a)     [CDnsim_a] by fol -;
    consider G such that
    G ∈ a ∧ G ∈ Open (C, D)     [CGD] by fol - a_line SameSide_DEF;
    G ∈ c ∧ Collinear G B A     [Gc] by fol c_line - BetweenLinear a_line Collinear_DEF;
    ¬Collinear B C D  ∧  ¬Collinear C D A  ∧  Open (A, B) ∩ Open (C, D) = ∅     [quadABCD] by fol H1 Quadrilateral_DEF Tetralateral_DEF;
    A ∉ c ∧ B ∉ c ∧ ¬(A = G) ∧ ¬(B = G)     [Distinct] by fol - c_line Collinear_DEF ∉ Gc;
    G ∉ Open (A, B)     [] by fol quadABCD CGD DisjointOneNotOther;
    A ∈ ray G B ━ {G}      [] by fol Distinct Gc - IN_Ray IN_DIFF IN_SING;
    fol c_line Gc Distinct - RaySameSide;
  qed;
`;;

let ConvexImpliesQuad = theorem `;
  ∀A B C D. Tetralateral A B C D  ⇒
    C ∈ int_angle D A B  ∧  D ∈ int_angle A B C
    ⇒  Quadrilateral A B C D

  proof
    intro_TAC ∀A B C D, H1, H2;
    ¬(A = B) ∧ ¬(B = C) ∧ ¬(A = D)     [TetraABCD] by fol H1 Tetralateral_DEF;
    consider a such that
    Line a ∧ A ∈ a ∧ B ∈ a     [a_line] by fol TetraABCD I1;
    consider b such that
    Line b ∧ B ∈ b ∧ C ∈ b     [b_line] by fol TetraABCD I1;
    consider d such that
    Line d ∧ D ∈ d ∧ A ∈ d     [d_line] by fol TetraABCD I1;
    Open (B, C) ⊂ b  ∧  Open (A, B) ⊂ a     [BCbABa] by fol b_line a_line BetweenLinear SUBSET;
    D,A same_side b  ∧  C,D same_side a     [] by fol H2 a_line b_line d_line InteriorUse;
    b ∩ Open (D, A) = ∅  ∧  a ∩ Open (C, D) = ∅     [] by fol - b_line SameSide_DEF IN_INTER MEMBER_NOT_EMPTY;
    fol H1 BCbABa - INTER_TENSOR SUBSET_REFL SUBSET_EMPTY Quadrilateral_DEF;
  qed;
`;;

let DiagonalsIntersectImpliesConvexQuad = theorem `;
  ∀A B C D G. ¬Collinear B C D  ⇒
    G ∈ Open (A, C)  ∧  G ∈ Open (B, D)
    ⇒  ConvexQuadrilateral A B C D

  proof
    intro_TAC ∀A B C D G, BCDncol, DiagInt;
    ¬(B = C) ∧ ¬(B = D) ∧ ¬(C = D) ∧ ¬(C = A) ∧ ¬(A = G) ∧ ¬(D = G) ∧ ¬(B = G)     [Distinct] by fol BCDncol NonCollinearImpliesDistinct DiagInt B1';
    Collinear A G C ∧ Collinear B G D     [Gcols] by fol DiagInt B1';
    ¬Collinear C D G ∧ ¬Collinear B C G     [Gncols] by fol BCDncol CollinearSymmetry Distinct Gcols  NoncollinearityExtendsToLine;
    ¬Collinear C D A     [CDAncol] by fol - CollinearSymmetry Distinct Gcols  NoncollinearityExtendsToLine;
    ¬Collinear A B C ∧ ¬Collinear D A G     [ABCncol] by fol Gncols - CollinearSymmetry Distinct Gcols NoncollinearityExtendsToLine;
    ¬Collinear D A B     [DABncol] by fol - CollinearSymmetry Distinct Gcols NoncollinearityExtendsToLine;
    ¬(A = B) ∧ ¬(A = D)     [] by fol DABncol NonCollinearImpliesDistinct;
    Tetralateral A B C D     [TetraABCD] by fol Distinct - BCDncol CDAncol DABncol ABCncol Tetralateral_DEF;
    A ∈ ray C G ━ {C}  ∧  B ∈ ray D G ━ {D}  ∧  C ∈ ray A G ━ {A}  ∧  D ∈ ray B G ━ {B}     [ArCG] by fol DiagInt B1' IntervalRayEZ;
    G ∈ int_angle B C D ∧ G ∈ int_angle C D A ∧ G ∈ int_angle D A B ∧ G ∈ int_angle A B C     [] by fol BCDncol CDAncol DABncol ABCncol DiagInt B1' ConverseCrossbar;
    A ∈ int_angle B C D ∧ B ∈ int_angle C D A ∧ C ∈ int_angle D A B ∧ D ∈ int_angle A B C     [] by fol - ArCG WholeRayInterior;
    fol TetraABCD - ConvexImpliesQuad ConvexQuad_DEF;
  qed;
`;;

let DoubleNotSimImpliesDiagonalsIntersect = theorem `;
  ∀A B C D l m.  Line l ∧ A ∈ l ∧ C ∈ l  ⇒  Line m ∧ B ∈ m ∧ D ∈ m  ⇒
    Tetralateral A B C D  ⇒  ¬(B,D same_side l)  ⇒  ¬(A,C same_side m)
    ⇒  (∃G. G ∈ Open (A, C) ∩ Open (B, D)) ∧ ConvexQuadrilateral A B C D

  proof
    intro_TAC ∀A B C D l m, l_line, m_line, H1, H2, H3;
    ¬Collinear A B C ∧ ¬Collinear B C D ∧ ¬Collinear C D A ∧ ¬Collinear D A B     [TetraABCD] by fol H1 Tetralateral_DEF;
    consider G such that
    G ∈ Open (A, C) ∧ G ∈ m     [AGC] by fol H3 m_line SameSide_DEF;
    G ∈ l     [Gl] by fol l_line - BetweenLinear;
    A ∉ m ∧ B ∉ l ∧ D ∉ l     [] by fol TetraABCD m_line l_line Collinear_DEF ∉;
    ¬(l = m) ∧ B ∈ m ━ {G} ∧ D ∈ m ━ {G}     [BDm_G] by fol - l_line ∉ m_line Gl IN_DIFF IN_SING;
    l ∩ m = {G}     [] by fol l_line m_line - Gl AGC I1Uniqueness;
    G ∈ Open (B, D)     [] by fol l_line m_line - BDm_G H2 EquivIntersection ∉;
    fol AGC - IN_INTER TetraABCD DiagonalsIntersectImpliesConvexQuad;
  qed;
`;;

let ConvexQuadImpliesDiagonalsIntersect = theorem `;
  ∀A B C D l m.  Line l ∧ A ∈ l ∧ C ∈ l  ⇒  Line m ∧ B ∈ m ∧ D ∈ m  ⇒
    ConvexQuadrilateral A B C D
    ⇒  ¬(B,D same_side l) ∧ ¬(A,C same_side m) ∧
       (∃G. G ∈ Open (A, C) ∩ Open (B, D)) ∧ ¬Quadrilateral A B D C

  proof
    intro_TAC ∀A B C D l m, l_line, m_line, ConvQuadABCD;
    Tetralateral A B C D ∧ A ∈ int_angle B C D ∧ D ∈ int_angle A B C     [convquadABCD] by fol ConvQuadABCD ConvexQuad_DEF Quadrilateral_DEF;
    ¬(B,D same_side l)  ∧  ¬(A,C same_side m)     [opp_sides] by fol convquadABCD l_line m_line InteriorOpposite;
    consider G such that
    G ∈ Open (A, C) ∩ Open (B, D)     [Gexists] by fol l_line m_line convquadABCD opp_sides DoubleNotSimImpliesDiagonalsIntersect;
    ¬(Open (B, D) ∩ Open (C, A) = ∅)     [] by fol - IN_INTER B1' MEMBER_NOT_EMPTY;
    ¬Quadrilateral A B D C     [] by fol - Quadrilateral_DEF;
    fol opp_sides Gexists -;
  qed;
`;;

let FourChoicesTetralateralHelp = theorem `;
  ∀A B C D. Tetralateral A B C D  ∧  C ∈ int_angle D A B
    ⇒  ConvexQuadrilateral A B C D ∨ C ∈ int_triangle D A B

  proof
    intro_TAC ∀A B C D, H1 CintDAB;
    ¬(A = B) ∧ ¬(D = A) ∧ ¬(A = C) ∧ ¬(B = D) ∧ ¬Collinear A B C ∧ ¬Collinear B C D ∧ ¬Collinear C D A ∧ ¬Collinear D A B     [TetraABCD] by fol H1 Tetralateral_DEF;
    consider a d such that
    Line a ∧ A ∈ a ∧ B ∈ a  ∧
    Line d ∧ D ∈ d ∧ A ∈ d     [ad_line] by fol TetraABCD I1;
    consider l m such that
    Line l ∧ A ∈ l ∧ C ∈ l  ∧
    Line m ∧ B ∈ m ∧ D ∈ m     [lm_line] by fol TetraABCD I1;
    C ∉ a ∧ C ∉ d ∧ B ∉ l ∧ D ∉ l ∧ A ∉ m ∧ C ∉ m ∧ ¬Collinear A B D ∧ ¬Collinear B D A          [tetra'] by fol TetraABCD ad_line lm_line Collinear_DEF ∉ CollinearSymmetry;
    ¬(B,D same_side l)     [Bsim_lD] by fol CintDAB lm_line InteriorOpposite - SameSideSymmetric;
    assume A,C same_side m     [same] by fol lm_line H1 Bsim_lD - DoubleNotSimImpliesDiagonalsIntersect;
    C,A same_side m     [Csim_mA] by fol lm_line - tetra' SameSideSymmetric;
    C,B same_side d  ∧  C,D same_side a     [] by fol ad_line CintDAB InteriorUse;
    C ∈ int_angle A B D  ∧  C ∈ int_angle B D A     [] by fol tetra' ad_line lm_line Csim_mA - IN_InteriorAngle;
    fol CintDAB - IN_InteriorTriangle;
  qed;
`;;
let FourChoicesTetralateralHelp = theorem `;
  ∀A B C D. Tetralateral A B C D  ∧  C ∈ int_angle D A B
    ⇒  ConvexQuadrilateral A B C D ∨ C ∈ int_triangle D A B

  proof
    intro_TAC ∀A B C D, H1 CintDAB;
    ¬(A = B) ∧ ¬(D = A) ∧ ¬(A = C) ∧ ¬(B = D) ∧ ¬Collinear A B C ∧ ¬Collinear B C D ∧ ¬Collinear C D A ∧ ¬Collinear D A B     [TetraABCD] by fol H1 Tetralateral_DEF;
    consider a d such that
    Line a ∧ A ∈ a ∧ B ∈ a  ∧
    Line d ∧ D ∈ d ∧ A ∈ d     [ad_line] by fol TetraABCD I1;
    consider l m such that
    Line l ∧ A ∈ l ∧ C ∈ l  ∧
    Line m ∧ B ∈ m ∧ D ∈ m     [lm_line] by fol TetraABCD I1;
    C ∉ a ∧ C ∉ d ∧ B ∉ l ∧ D ∉ l ∧ A ∉ m ∧ C ∉ m ∧ ¬Collinear A B D ∧ ¬Collinear B D A          [tetra'] by fol TetraABCD ad_line lm_line Collinear_DEF ∉ CollinearSymmetry;
    ¬(B,D same_side l)     [Bsim_lD] by fol CintDAB lm_line InteriorOpposite - SameSideSymmetric;
    assume A,C same_side m     [same] by fol lm_line H1 Bsim_lD - DoubleNotSimImpliesDiagonalsIntersect;
    C,A same_side m     [Csim_mA] by fol lm_line - tetra' SameSideSymmetric;
    C,B same_side d  ∧  C,D same_side a     [] by fol ad_line CintDAB InteriorUse;
    C ∈ int_angle A B D  ∧  C ∈ int_angle B D A     [] by fol tetra' ad_line lm_line Csim_mA - IN_InteriorAngle;
    fol CintDAB - IN_InteriorTriangle;
  qed;
`;;

let InteriorTriangleSymmetry = theorem `;
  ∀A B C P. P ∈ int_triangle A B C  ⇒ P ∈ int_triangle B C A
  by fol IN_InteriorTriangle`;;

let FourChoicesTetralateral = theorem `;
  ∀A B C D a. Tetralateral A B C D  ⇒
    Line a ∧ A ∈ a ∧ B ∈ a  ⇒  C,D same_side a
    ⇒  ConvexQuadrilateral A B C D  ∨  ConvexQuadrilateral A B D C  ∨
       D ∈ int_triangle A B C  ∨  C ∈ int_triangle D A B

  proof
    intro_TAC ∀A B C D a, H1, a_line, Csim_aD;
     ¬(A = B) ∧ ¬Collinear A B C ∧ ¬Collinear C D A ∧ ¬Collinear D A B ∧ Tetralateral A B D C     [TetraABCD] by fol H1 Tetralateral_DEF TetralateralSymmetry;
    ¬Collinear C A D ∧ C ∉ a ∧ D ∉ a     [notCDa] by fol TetraABCD CollinearSymmetry a_line Collinear_DEF ∉;
    C ∈ int_angle D A B  ∨  D ∈ int_angle C A B     [] by fol TetraABCD a_line - Csim_aD AngleOrdering;
    case_split CintDAB | DintCAB     by fol -;
    suppose C ∈ int_angle D A B;
      ConvexQuadrilateral A B C D  ∨  C ∈ int_triangle D A B     [] by fol H1 - FourChoicesTetralateralHelp;
      fol -;
    end;
    suppose D ∈ int_angle C A B;
      ConvexQuadrilateral A B D C  ∨  D ∈ int_triangle C A B     [] by fol TetraABCD - FourChoicesTetralateralHelp;
      fol - InteriorTriangleSymmetry;
    end;
  qed;
`;;

let QuadrilateralSymmetry = theorem `;
  ∀A B C D. Quadrilateral A B C D  ⇒
    Quadrilateral B C D A  ∧  Quadrilateral C D A B  ∧  Quadrilateral D A B C
  by fol Quadrilateral_DEF INTER_COMM TetralateralSymmetry Quadrilateral_DEF`;;

let FiveChoicesQuadrilateral = theorem `;
  ∀A B C D l m.  Quadrilateral A B C D  ⇒
    Line l ∧ A ∈ l ∧ C ∈ l  ∧  Line m ∧ B ∈ m ∧ D ∈ m
    ⇒  (ConvexQuadrilateral A B C D  ∨  A ∈ int_triangle B C D  ∨
       B ∈ int_triangle C D A  ∨  C ∈ int_triangle D A B  ∨
       D ∈ int_triangle A B C)  ∧
       (¬(B,D same_side l) ∨ ¬(A,C same_side m))

  proof
    intro_TAC ∀A B C D l m, H1, lm_line;
    Tetralateral A B C D     [H1Tetra] by fol H1 Quadrilateral_DEF;
    ¬(A = B) ∧ ¬(A = D) ∧ ¬(B = C) ∧ ¬(C = D)     [Distinct] by fol H1Tetra Tetralateral_DEF;
    consider a c such that
    Line a ∧ A ∈ a ∧ B ∈ a  ∧
    Line c ∧ C ∈ c ∧ D ∈ c     [ac_line] by fol Distinct I1;
    Quadrilateral C D A B  ∧  Tetralateral C D A B     [tetraCDAB] by fol H1 QuadrilateralSymmetry Quadrilateral_DEF;
    ¬ConvexQuadrilateral A B D C  ∧  ¬ConvexQuadrilateral C D B A     [notconvquad] by fol Distinct I1 H1 - ConvexQuadImpliesDiagonalsIntersect;
    ConvexQuadrilateral A B C D  ∨  A ∈ int_triangle B C D  ∨
    B ∈ int_triangle C D A  ∨  C ∈ int_triangle D A B  ∨
    D ∈ int_triangle A B C     [5choices]
    proof
      A,B same_side c  ∨  C,D same_side a     [2pos] by fol H1 ac_line SegmentSameSideOppositeLine;
      assume A,B same_side c     [Asym_cB] by fol 2pos H1Tetra ac_line - notconvquad FourChoicesTetralateral;
      ConvexQuadrilateral C D A B  ∨  B ∈ int_triangle C D A  ∨
      A ∈ int_triangle B C D     [X1] by fol tetraCDAB ac_line - notconvquad FourChoicesTetralateral;
      fol - QuadrilateralSymmetry ConvexQuad_DEF;
    qed;
    ¬(B,D same_side l) ∨ ¬(A,C same_side m)     [] by fol - lm_line ConvexQuadImpliesDiagonalsIntersect IN_InteriorTriangle InteriorAngleSymmetry InteriorOpposite;
    fol 5choices -;
  qed;
`;;

let IntervalSymmetry = theorem `;
  ∀A B. Open (A, B) = Open (B, A)
  by fol B1' EXTENSION`;;

let SegmentSymmetry = theorem `;
  ∀A B. seg A B = seg B A
  by fol Segment_DEF INSERT_COMM IntervalSymmetry`;;

let C1OppositeRay = theorem `;
  ∀O P s.  Segment s ∧ ¬(O = P)  ⇒  ∃Q. P ∈ Open (O, Q)  ∧  seg P Q ≡ s

  proof
    intro_TAC ∀O P s, H1;
    consider Z such that
    P ∈ Open (O, Z)  ∧  ¬(P = Z)     [OPZ] by fol H1 B2' B1';
    consider Q such that
    Q ∈ ray P Z ━ {P} ∧ seg P Q ≡ s     [PQeq] by fol H1 - C1;
    P ∈ Open (Q, O)     [] by fol OPZ - OppositeRaysIntersect1pointHelp;
    fol - B1' PQeq;
  qed;
`;;

let OrderedCongruentSegments = theorem `;
  ∀A B C D G.  ¬(A = C) ∧ ¬(D = G)  ⇒  seg A C ≡ seg D G  ⇒  B ∈ Open (A, C)
    ⇒  ∃E. E ∈ Open (D, G)  ∧  seg A B ≡ seg D E

  proof
    intro_TAC ∀A B C D G, H1, H2, H3;
    Segment (seg A B) ∧ Segment (seg A C) ∧ Segment (seg B C) ∧ Segment (seg D G)     [segs] by fol H3 B1' H1 SEGMENT;
    seg D G ≡ seg A C     [DGeqAC] by fol - H2 C2Symmetric;
    consider E such that
    E ∈ ray D G ━ {D} ∧ seg D E ≡ seg A B     [DEeqAB] by fol segs H1 C1;
    ¬(E = D) ∧ Collinear D E G ∧ D ∉ Open (G, E)     [ErDG] by fol - IN_DIFF IN_SING IN_Ray B1' CollinearSymmetry ∉;
    consider G' such that
    E ∈ Open (D, G') ∧ seg E G' ≡ seg B C     [DEG'] by fol segs - C1OppositeRay;
    seg D G' ≡ seg A C     [DG'eqAC] by fol DEG' H3 DEeqAB C3;
    Segment (seg D G') ∧ Segment (seg D E)     [] by fol DEG' B1' SEGMENT;
    seg A C ≡ seg D G' ∧ seg A B ≡ seg D E     [ABeqDE] by fol segs - DG'eqAC C2Symmetric DEeqAB;
    G' ∈ ray D E ━ {D}  ∧  G ∈ ray D E ━ {D}     [] by fol DEG' IntervalRayEZ ErDG IN_Ray H1 IN_DIFF IN_SING;
    G' = G     [] by fol ErDG segs - DG'eqAC DGeqAC C1;
    fol - DEG' ABeqDE;
  qed;
`;;

let SegmentSubtraction = theorem `;
  ∀A B C A' B' C'. B ∈ Open (A, C)  ∧  B' ∈ Open (A', C')  ⇒
    seg A B ≡ seg A' B'  ⇒  seg A C ≡ seg A' C'
    ⇒  seg B C ≡ seg B' C'

  proof
    intro_TAC ∀A B C A' B' C', H1, H2, H3;
    ¬(A = B) ∧ ¬(A = C) ∧ Collinear A B C ∧ Segment (seg A' C') ∧ Segment (seg B' C')     [Distinct] by fol H1 B1' SEGMENT;
    consider Q such that
    B ∈ Open (A, Q)  ∧  seg B Q ≡ seg B' C'     [defQ] by fol - C1OppositeRay;
    seg A Q ≡ seg A' C'     [AQ_A'C'] by fol H1 H2 - C3;
    ¬(A = Q)  ∧  Collinear A B Q  ∧  A ∉ Open (C, B)  ∧  A ∉ Open (Q, B)     []
    proof     simplify defQ B1' ∉;     fol defQ B1' H1 B3';     qed;
    C ∈ ray A B ━ {A}  ∧  Q ∈ ray A B ━ {A}     [] by fol Distinct - IN_Ray IN_DIFF IN_SING;
    fol defQ Distinct - AQ_A'C' H3 C1;
  qed;
`;;

let SegmentOrderingUse = theorem `;
  ∀A B s.  Segment s  ∧  ¬(A = B)  ⇒  s <__ seg A B
    ⇒  ∃G. G ∈ Open (A, B)  ∧  s ≡ seg A G

  proof
    intro_TAC ∀A B s, H1, H2;
    consider A' B' G' such that
    seg A B = seg A' B'  ∧  G' ∈ Open (A', B')  ∧  s ≡ seg A' G'     [H2'] by fol H2 SegmentOrdering_DEF;
    ¬(A' = G') ∧ ¬(A' = B')  ∧  seg A' B' ≡ seg A B     [A'notB'G'] by fol - B1' H1 SEGMENT C2Reflexive;
    consider G such that
    G ∈ Open (A, B)  ∧  seg A' G' ≡ seg A G     [AGB] by fol A'notB'G' H1 H2' -  OrderedCongruentSegments;
    s ≡ seg A G     [] by fol H1 A'notB'G' - B1' SEGMENT H2' C2Transitive;
    fol AGB -;
  qed;
`;;

let SegmentTrichotomy1 = theorem `;
  ∀s t.  s <__ t  ⇒  ¬(s ≡ t)

  proof
    intro_TAC ∀s t, H1;
    consider A B G such that
    Segment s ∧ t = seg A B ∧ G ∈ Open (A, B) ∧ s ≡ seg A G     [H1'] by fol H1 SegmentOrdering_DEF;
    ¬(A = G) ∧ ¬(A = B) ∧ ¬(G = B)     [Distinct] by fol H1' B1';
    seg A B ≡ seg A B     [ABrefl] by fol - SEGMENT C2Reflexive;
    G ∈ ray A B ━ {A}  ∧  B ∈ ray A B ━ {A}     [] by fol H1' IntervalRay EndpointInRay Distinct IN_DIFF IN_SING;
    ¬(seg A G ≡ seg A B)  ∧ seg A G ≡ s     [] by fol Distinct SEGMENT - ABrefl C1 H1' C2Symmetric;
    fol Distinct H1' SEGMENT - C2Transitive;
  qed;
`;;

let SegmentTrichotomy2 = theorem `;
  ∀s t u.  s <__ t  ∧  Segment u  ∧  t ≡ u  ⇒  s <__ u

  proof
    intro_TAC ∀s t u, H1 H2;
    consider A B P such that
    Segment s  ∧  t = seg A B  ∧  P ∈ Open (A, B)  ∧  s ≡ seg A P     [H1'] by fol H1 SegmentOrdering_DEF;
    ¬(A = B) ∧ ¬(A = P)     [Distinct] by fol - B1';
    consider X Y such that
    u = seg X Y ∧ ¬(X = Y)     [uXY] by fol H2 SEGMENT;
    consider Q such that
    Q ∈ Open (X, Y)  ∧  seg A P ≡ seg X Q     [XQY] by fol Distinct - H1' H2 OrderedCongruentSegments;
    ¬(X = Q)  ∧  s ≡ seg X Q     [] by fol - B1' H1' Distinct SEGMENT XQY C2Transitive;
    fol H1' uXY XQY - SegmentOrdering_DEF;
  qed;
`;;

let SegmentOrderTransitivity = theorem `;
  ∀s t u.  s <__ t  ∧  t <__ u  ⇒  s <__ u

  proof
    intro_TAC ∀s t u, H1;
    consider A B G such that
    u = seg A B  ∧  G ∈ Open (A, B)  ∧  t ≡ seg A G     [H1'] by fol H1 SegmentOrdering_DEF;
    ¬(A = B) ∧ ¬(A = G) ∧ Segment s     [Distinct] by fol H1'  B1' H1 SegmentOrdering_DEF;
    s <__ seg A G     [] by fol H1 H1' Distinct SEGMENT SegmentTrichotomy2;
    consider F such that
    F ∈ Open (A, G) ∧ s ≡ seg A F     [AFG] by fol Distinct - SegmentOrderingUse;
    F ∈ Open (A, B)     [] by fol H1' IntervalsAreConvex - SUBSET;
    fol Distinct H1' - AFG SegmentOrdering_DEF;
  qed;
`;;

let SegmentTrichotomy = theorem `;
  ∀s t.  Segment s ∧ Segment t
    ⇒  (s ≡ t  ∨  s <__ t  ∨  t <__ s)  ∧  ¬(s ≡ t ∧ s <__ t)  ∧
       ¬(s ≡ t ∧ t <__ s)  ∧  ¬(s <__ t ∧ t <__ s)

  proof
    intro_TAC ∀s t, H1;
    ¬(s ≡ t  ∧  s <__ t)     [Not12] by fol - SegmentTrichotomy1;
    ¬(s ≡ t  ∧  t <__ s)     [Not13] by fol H1 - SegmentTrichotomy1 C2Symmetric;
    ¬(s <__ t  ∧  t <__ s)     [Not23] by fol H1 - SegmentOrderTransitivity SegmentTrichotomy1 H1 C2Reflexive;
    consider O P such that
    s = seg O P  ∧  ¬(O = P)     [sOP] by fol H1 SEGMENT;
    consider Q such that
    Q ∈ ray O P ━ {O}  ∧  seg O Q ≡ t     [QrOP] by fol H1 - C1;
    O ∉ Open (Q, P)  ∧  Collinear O P Q   ∧  ¬(O = Q)     [notQOP] by fol - IN_DIFF IN_SING IN_Ray;
    s ≡ seg O P  ∧  t ≡ seg O Q  ∧  seg O Q ≡ t  ∧  seg O P ≡ s     [stOPQ] by fol H1 sOP - SEGMENT QrOP C2Reflexive C2Symmetric;
    assume ¬(Q = P) [notQP] by fol stOPQ - sOP QrOP Not12 Not13 Not23;
    P ∈ Open (O, Q)  ∨  Q ∈ Open (O, P)     [] by fol sOP - notQOP B3' B1' ∉;
    s <__ seg O Q  ∨  t <__ seg O P     [] by fol H1 - stOPQ SegmentOrdering_DEF;
    s <__ t  ∨  t <__ s     [] by fol - H1 stOPQ SegmentTrichotomy2;
    fol - Not12 Not13 Not23;
  qed;
`;;


let C4Uniqueness = theorem `;
  ∀O A B P l.  Line l ∧ O ∈ l ∧ A ∈ l ∧ ¬(O = A)  ⇒
    B ∉ l ∧ P ∉ l ∧ P,B same_side l  ⇒  ∡ A O P ≡ ∡ A O B
    ⇒  ray O B = ray O P

  proof
    intro_TAC ∀O A B P l, H1, H2, H3;
    ¬(O = B) ∧ ¬(O = P) ∧ Ray (ray O B) ∧ Ray (ray O P)     [Distinct] by fol H2 H1 ∉ RAY;
    ¬Collinear A O B  ∧  B,B same_side l     [Bsim_lB] by fol H1 H2 I1 Collinear_DEF ∉ SameSideReflexive;
    Angle (∡ A O B)  ∧  ∡ A O B ≡ ∡ A O B     [] by fol - ANGLE C5Reflexive;
    fol - H1 H2 Distinct Bsim_lB H3 C4;
  qed;
`;;

let AngleSymmetry = theorem `;
  ∀A O B. ∡ A O B = ∡ B O A
  by fol Angle_DEF UNION_COMM`;;

let TriangleCongSymmetry = theorem `;
  ∀A B C A' B' C'. A,B,C ≅ A',B',C'
   ⇒  A,C,B ≅ A',C',B' ∧ B,A,C ≅ B',A',C' ∧
       B,C,A ≅ B',C',A' ∧ C,A,B ≅ C',A',B' ∧ C,B,A ≅ C',B',A'

  proof
    intro_TAC ∀A B C A' B' C', H1;
    ¬Collinear A B C ∧ ¬Collinear A' B' C' ∧
    seg A B ≡ seg A' B' ∧ seg A C ≡ seg A' C' ∧ seg B C ≡ seg B' C' ∧
    ∡ A B C ≡ ∡ A' B' C' ∧ ∡ B C A ≡ ∡ B' C' A' ∧ ∡ C A B ≡ ∡ C' A' B'     [H1'] by fol H1 TriangleCong_DEF;
    seg B A ≡ seg B' A' ∧ seg C A ≡ seg C' A' ∧ seg C B ≡ seg C' B'     [segments] by fol H1' SegmentSymmetry;
    ∡ C B A ≡ ∡ C' B' A' ∧ ∡ A C B ≡ ∡ A' C' B' ∧ ∡ B A C ≡ ∡ B' A' C'     [] by fol H1' AngleSymmetry;
    fol CollinearSymmetry H1' segments - TriangleCong_DEF;
  qed;
`;;

let SAS = theorem `;
  ∀A B C A' B' C'. ¬Collinear A B C ∧ ¬Collinear A' B' C'  ⇒
    seg B A ≡ seg B' A'  ∧  seg B C ≡ seg B' C'  ⇒ ∡ A B C ≡ ∡ A' B' C'
    ⇒  A,B,C ≅ A',B',C'

  proof
    intro_TAC ∀A B C A' B' C', H1, H2, H3;
    ¬(A = B) ∧ ¬(A = C) ∧ ¬(A' = C')     [Distinct] by fol H1 NonCollinearImpliesDistinct;
    consider c such that
    Line c ∧ A ∈ c ∧ B ∈ c     [c_line] by fol Distinct I1;
    C ∉ c     [notCc] by fol H1 c_line Collinear_DEF ∉;
    ∡ B C A ≡ ∡ B' C' A'     [BCAeq] by fol H1 H2 H3 C6;
    ∡ B A C ≡ ∡ B' A' C'     [BACeq] by fol H1 CollinearSymmetry H2 H3 AngleSymmetry C6;
    consider Y such that
    Y ∈ ray A C ━ {A}  ∧  seg A Y ≡ seg A' C'     [YrAC] by fol Distinct SEGMENT C1;
    Y ∉ c  ∧  Y,C same_side c     [Ysim_cC] by fol c_line notCc - RaySameSide;
    ¬Collinear Y A B     [YABncol] by fol Distinct c_line - NonCollinearRaa CollinearSymmetry;
    ray A Y = ray A C  ∧  ∡ Y A B = ∡ C A B     [] by fol Distinct YrAC RayWellDefined Angle_DEF;
    ∡ Y A B ≡ ∡ C' A' B'     [] by fol BACeq - AngleSymmetry;
    ∡ A B Y ≡ ∡ A' B' C'     [ABYeq] by fol YABncol H1 CollinearSymmetry H2 SegmentSymmetry YrAC - C6;
    Angle (∡ A B C) ∧ Angle (∡ A' B' C') ∧ Angle (∡ A B Y)     [] by fol H1 CollinearSymmetry YABncol ANGLE;
    ∡ A B Y ≡ ∡ A B C     [ABYeqABC] by fol - ABYeq - H3 C5Symmetric C5Transitive;
    ray B C = ray B Y  ∧  ¬(Y = B)  ∧  Y ∈ ray B C     [] by fol c_line Distinct notCc Ysim_cC ABYeqABC C4Uniqueness ∉ - EndpointInRay;
    Collinear B C Y  ∧  Collinear A C Y     [ABCYcol] by fol - YrAC IN_DIFF IN_SING IN_Ray;
    C = Y     [] by fol H1 ABCYcol TwoSidesTriangle1Intersection;
    seg A C ≡ seg A' C'     [] by fol - YrAC;
    fol H1 H2 SegmentSymmetry - H3 BCAeq BACeq AngleSymmetry TriangleCong_DEF;
  qed;
`;;

let ASA = theorem `;
  ∀A B C A' B' C'. ¬Collinear A B C ∧ ¬Collinear A' B' C'  ⇒
    seg A C ≡ seg A' C'  ⇒  ∡ C A B ≡ ∡ C' A' B'  ∧  ∡ B C A ≡ ∡ B' C' A'
    ⇒  A,B,C ≅ A',B',C'

  proof
    intro_TAC ∀A B C A' B' C', H1, H2, H3;
    ¬(A = B) ∧ ¬(A = C) ∧ ¬(B = C) ∧ ¬(A' = B') ∧ ¬(A' = C') ∧ ¬(B' = C') ∧
    Segment (seg C' B')     [Distinct] by fol H1 NonCollinearImpliesDistinct SEGMENT;
    consider D such that
    D ∈ ray C B ━ {C}  ∧  seg C D ≡ seg C' B'  ∧  ¬(D = C)     [DrCB] by fol - C1 IN_DIFF IN_SING;
    Collinear C B D     [CBDcol] by fol - IN_DIFF IN_SING IN_Ray;
    ¬Collinear D C A ∧ Angle (∡ C A D) ∧ Angle (∡ C' A' B') ∧ Angle (∡ C A B)     [DCAncol] by fol H1 CollinearSymmetry - DrCB NoncollinearityExtendsToLine H1 ANGLE;
    consider b such that
    Line b ∧ A ∈ b ∧ C ∈ b     [b_line] by fol Distinct I1;
    B ∉ b ∧ ¬(D = A)     [notBb] by fol H1 - Collinear_DEF ∉ DCAncol NonCollinearImpliesDistinct;
    D ∉ b  ∧  D,B same_side b     [Dsim_bB] by fol b_line - DrCB RaySameSide;
    ray C D = ray C B     [] by fol Distinct DrCB RayWellDefined;
    ∡ D C A ≡ ∡ B' C' A'     [] by fol H3 - Angle_DEF;
    D,C,A ≅ B',C',A'     [] by fol DCAncol H1 CollinearSymmetry DrCB H2 SegmentSymmetry - SAS;
    ∡ C A D ≡ ∡ C' A' B'     [] by fol - TriangleCong_DEF;
    ∡ C A D ≡ ∡ C A B     [] by fol DCAncol - H3 C5Symmetric C5Transitive;
    ray A B = ray A D  ∧  D ∈ ray A B     [] by fol b_line Distinct notBb Dsim_bB - C4Uniqueness notBb EndpointInRay;
    Collinear A B D     [ABDcol] by fol - IN_Ray;
    D = B     [] by fol H1 CBDcol ABDcol CollinearSymmetry TwoSidesTriangle1Intersection;
    seg C B ≡ seg C' B'     [] by fol - DrCB;
    B,C,A ≅ B',C',A'     [] by fol H1 CollinearSymmetry - H2 SegmentSymmetry H3 SAS;
    fol - TriangleCongSymmetry;
  qed;
`;;

let AngleSubtraction = theorem `;
  ∀A O B A' O' B' G G'. G ∈ int_angle A O B  ∧  G' ∈ int_angle A' O' B'  ⇒
    ∡ A O B ≡ ∡ A' O' B'  ∧  ∡ A O G ≡ ∡ A' O' G'
    ⇒  ∡ G O B ≡ ∡ G' O' B'

  proof
    intro_TAC ∀A O B A' O' B' G G', H1, H2;
    ¬Collinear A O B ∧ ¬Collinear A' O' B'     [A'O'B'ncol] by fol H1 IN_InteriorAngle;
    ¬(A = O) ∧ ¬(O = B) ∧ ¬(G = O) ∧ ¬(G' = O') ∧ Segment (seg O' A') ∧ Segment (seg O' B')     [Distinct] by fol - NonCollinearImpliesDistinct H1 InteriorEZHelp SEGMENT;
   consider X Y such that
   X ∈ ray O A ━ {O}  ∧  seg O X ≡ seg O' A'  ∧  Y ∈ ray O B ━ {O}  ∧  seg O Y ≡ seg O' B'     [XYexists] by fol - C1;
    G ∈ int_angle X O Y     [GintXOY] by fol H1 XYexists InteriorWellDefined InteriorAngleSymmetry;
    consider H H' such that
    H ∈ Open (X, Y)  ∧  H ∈ ray O G ━ {O}  ∧
    H' ∈ Open (A', B')  ∧  H' ∈ ray O' G' ━ {O'}     [Hexists] by fol - H1 Crossbar_THM;
    H ∈ int_angle X O Y  ∧  H' ∈ int_angle A' O' B'     [HintXOY] by fol GintXOY H1 - WholeRayInterior;
    ray O X = ray O A  ∧  ray O Y = ray O B  ∧  ray O H = ray O G  ∧  ray O' H' = ray O' G'     [Orays] by fol Distinct XYexists Hexists RayWellDefined;
    ∡ X O Y ≡ ∡ A' O' B'  ∧  ∡ X O H ≡ ∡ A' O' H'     [H2'] by fol H2 - Angle_DEF;
    ¬Collinear X O Y     [] by fol GintXOY IN_InteriorAngle;
    X,O,Y ≅ A',O',B'     [] by fol - A'O'B'ncol H2' XYexists SAS;
    seg X Y ≡ seg A' B'  ∧  ∡ O Y X ≡ ∡ O' B' A'  ∧  ∡ Y X O ≡ ∡ B' A' O'     [XOYcong] by fol - TriangleCong_DEF;
    ¬Collinear O H X ∧ ¬Collinear O' H' A' ∧ ¬Collinear O Y H ∧ ¬Collinear O' B' H'     [OHXncol] by fol HintXOY InteriorEZHelp InteriorAngleSymmetry CollinearSymmetry;
    ray X H = ray X Y  ∧  ray A' H' = ray A' B'  ∧  ray Y H = ray Y X  ∧  ray B' H' = ray B' A'     [Hrays] by fol Hexists B1' IntervalRay;
    ∡ H X O ≡ ∡ H' A' O'     [] by fol XOYcong - Angle_DEF;
    O,H,X ≅ O',H',A'     [] by fol OHXncol XYexists - H2' ASA;
    seg X H ≡ seg A' H'     [] by fol - TriangleCong_DEF SegmentSymmetry;
    seg H Y ≡ seg H' B'     [] by fol Hexists XOYcong - SegmentSubtraction;
    seg Y O  ≡ seg B' O'  ∧  seg Y H ≡ seg B' H'     [YHeq] by fol XYexists - SegmentSymmetry;
    ∡ O Y H ≡ ∡ O' B' H'     [] by fol XOYcong Hrays Angle_DEF;
    O,Y,H ≅ O',B',H'     [] by fol OHXncol YHeq - SAS;
  ∡ H O Y ≡ ∡ H' O' B'     [] by fol - TriangleCong_DEF;
  fol - Orays Angle_DEF;
  qed;
`;;

let OrderedCongruentAngles = theorem `;
  ∀A O B A' O' B' G. ¬Collinear A' O' B'  ∧  ∡ A O B ≡ ∡ A' O' B'  ∧ G ∈ int_angle A O B
    ⇒  ∃G'. G' ∈ int_angle A' O' B'  ∧  ∡ A O G ≡ ∡ A' O' G'

  proof
    intro_TAC ∀A O B A' O' B' G, H1 H2 H3;
    ¬Collinear A O B     [AOBncol] by fol H3 IN_InteriorAngle;
    ¬(A = O) ∧ ¬(O = B) ∧ ¬(A' = B') ∧ ¬(O = G) ∧ Segment (seg O' A') ∧ Segment (seg O' B')     [Distinct] by fol AOBncol H1 NonCollinearImpliesDistinct H3 InteriorEZHelp SEGMENT;
    consider X Y such that
    X ∈ ray O A ━ {O}  ∧  seg O X ≡ seg O' A'  ∧  Y ∈ ray O B ━ {O}  ∧  seg O Y ≡ seg O' B'     [defXY] by fol - C1;
    G ∈ int_angle X O Y     [GintXOY] by fol H3 - InteriorWellDefined InteriorAngleSymmetry;
    ¬Collinear X O Y ∧ ¬(X = Y)     [XOYncol] by fol - IN_InteriorAngle NonCollinearImpliesDistinct;
    consider H such that
    H ∈ Open (X, Y)  ∧  H ∈ ray O G ━ {O}     [defH] by fol GintXOY Crossbar_THM;
    ray O X = ray O A  ∧  ray O Y = ray O B  ∧  ray O H = ray O G     [Orays] by fol Distinct defXY - RayWellDefined;
    ∡ X O Y ≡ ∡ A' O' B'     [] by fol H2 - Angle_DEF;
    X,O,Y ≅ A',O',B'     [] by fol XOYncol H1 defXY - SAS;
    seg X Y ≡ seg A' B'  ∧  ∡ O X Y ≡ ∡ O' A' B'     [YXOcong] by fol - TriangleCong_DEF AngleSymmetry;
    consider G' such that
    G' ∈ Open (A', B')  ∧  seg X H ≡ seg A' G'     [A'G'B'] by fol XOYncol Distinct - defH OrderedCongruentSegments;
    G' ∈ int_angle A' O' B'     [G'intA'O'B'] by fol H1 - ConverseCrossbar;
    ray X H = ray X Y  ∧  ray A' G' = ray A' B'     [] by fol defH A'G'B' IntervalRay;
    ∡ O X H ≡ ∡ O' A' G'     [HXOeq] by fol - Angle_DEF YXOcong;
    H ∈ int_angle X O Y     [] by fol GintXOY defH WholeRayInterior;
    ¬Collinear O X H ∧ ¬Collinear O' A' G'     [] by fol - G'intA'O'B' InteriorEZHelp CollinearSymmetry;
    O,X,H ≅ O',A',G'     [] by fol - A'G'B' defXY SegmentSymmetry HXOeq SAS;
    ∡ X O H ≡ ∡ A' O' G'     [] by fol - TriangleCong_DEF AngleSymmetry;
    fol G'intA'O'B' - Orays Angle_DEF;
  qed;
`;;

let AngleAddition = theorem `;
  ∀A O B A' O' B' G G'.  G ∈ int_angle A O B  ∧  G' ∈ int_angle A' O' B'  ⇒
    ∡ A O G ≡ ∡ A' O' G'  ∧  ∡ G O B ≡ ∡ G' O' B'
   ⇒  ∡ A O B ≡ ∡ A' O' B'

  proof
    intro_TAC ∀A O B A' O' B' G G', H1, H2;
    ¬Collinear A O B ∧ ¬Collinear A' O' B'     [AOBncol] by fol H1 IN_InteriorAngle;
    ¬(A = O) ∧ ¬(A = B) ∧ ¬(O = B) ∧ ¬(A' = O') ∧ ¬(A' = B') ∧ ¬(O' = B') ∧ ¬(G = O)     [Distinct] by fol - NonCollinearImpliesDistinct H1 InteriorEZHelp;
    consider a b such that
    Line a ∧ O ∈ a ∧ A ∈ a  ∧
    Line b ∧ O ∈ b ∧ B ∈ b     [a_line] by fol Distinct I1;
    consider g such that
    Line g ∧ O ∈ g ∧ G ∈ g     [g_line] by fol  Distinct I1;
    G ∉ a ∧ G,B same_side a     [H1'] by fol a_line H1 InteriorUse;
    ¬Collinear A O G ∧ ¬Collinear A' O' G'     [AOGncol] by fol H1 InteriorEZHelp IN_InteriorAngle;
    Angle (∡ A O B) ∧ Angle (∡ A' O' B') ∧ Angle (∡ A O G) ∧ Angle (∡ A' O' G')     [angles] by fol AOBncol - ANGLE;
    ∃! r. Ray r ∧ ∃X. ¬(O = X) ∧ r = ray O X ∧ X ∉ a ∧ X,G same_side a ∧ ∡ A O X ≡ ∡ A' O' B'     [] by simplify C4 - angles Distinct a_line H1';
    consider X such that
    X ∉ a ∧ X,G same_side a ∧ ∡ A O X ≡ ∡ A' O' B'     [Xexists] by fol -;
    ¬Collinear A O X     [AOXncol] by fol Distinct a_line Xexists NonCollinearRaa CollinearSymmetry;
    ∡ A' O' B' ≡ ∡ A O X     [] by fol - AOBncol ANGLE Xexists C5Symmetric;
    consider Y such that
    Y ∈ int_angle A O X  ∧  ∡ A' O' G' ≡ ∡ A O Y     [YintAOX] by fol AOXncol - H1 OrderedCongruentAngles;
    ¬Collinear A O Y     [] by fol - InteriorEZHelp;
    ∡ A O Y  ≡ ∡ A O G     [AOGeq] by fol - angles - ANGLE YintAOX H2 C5Transitive C5Symmetric;
    consider x such that
    Line x ∧ O ∈ x ∧ X ∈ x     [x_line] by fol Distinct I1;
    Y ∉ a ∧ Y,X same_side a     [] by fol a_line - YintAOX InteriorUse;
    Y ∉ a ∧ Y,G same_side a     [] by fol  a_line - Xexists H1' SameSideTransitive;
    ray O G = ray O Y     [] by fol a_line Distinct H1' - AOGeq C4Uniqueness;
    G ∈ ray O Y ━ {O}     [] by fol Distinct - EndpointInRay IN_DIFF IN_SING;
    G ∈ int_angle A O X     [GintAOX] by fol YintAOX - WholeRayInterior;
    ∡ G O X ≡ ∡ G' O' B'     [GOXeq] by fol - H1 Xexists H2 AngleSubtraction;
    ¬Collinear G O X ∧ ¬Collinear G O B ∧ ¬Collinear G' O' B'     [GOXncol] by fol GintAOX H1 InteriorAngleSymmetry InteriorEZHelp CollinearSymmetry;
    Angle (∡ G O X) ∧ Angle (∡ G O B) ∧ Angle (∡ G' O' B')     [] by fol - ANGLE;
    ∡ G O X ≡ ∡ G O B     [G'O'Xeq] by fol  angles - GOXeq C5Symmetric H2 C5Transitive;
    ¬(A,X same_side g) ∧ ¬(A,B same_side g)     [Ansim_aXB] by fol g_line GintAOX H1 InteriorOpposite;
    A ∉ g ∧ B ∉ g ∧ X ∉ g     [notABXg] by fol g_line AOGncol GOXncol Distinct I1 Collinear_DEF ∉;
    X,B same_side g     [] by fol g_line - Ansim_aXB AtMost2Sides;
    ray O X = ray O B     [] by fol g_line Distinct notABXg - G'O'Xeq C4Uniqueness;
    fol - Xexists Angle_DEF;
  qed;
`;;

let AngleOrderingUse = theorem `;
  ∀A O B α.  Angle α  ∧  ¬Collinear A O B  ⇒  α <_ang ∡ A O B
    ⇒  ∃G. G ∈ int_angle A O B ∧ α ≡ ∡ A O G

  proof
    intro_TAC ∀A O B α, H1, H3;
    consider A' O' B' G' such that
    ¬Collinear A' O' B'  ∧  ∡ A O B = ∡ A' O' B'  ∧  G' ∈ int_angle A' O' B'  ∧  α ≡ ∡ A' O' G'     [H3'] by fol H3 AngleOrdering_DEF;
    Angle (∡ A O B) ∧ Angle (∡ A' O' B') ∧ Angle (∡ A' O' G')     [angles] by fol H1 - ANGLE InteriorEZHelp;
    ∡ A' O' B' ≡ ∡ A O B     [] by fol - H3' C5Reflexive;
    consider G such that
    G ∈ int_angle A O B  ∧  ∡ A' O' G' ≡ ∡ A O G     [GintAOB] by fol H1 H3' -  OrderedCongruentAngles;
    α ≡ ∡ A O G     [] by fol H1 angles - InteriorEZHelp ANGLE H3' GintAOB C5Transitive;
    fol - GintAOB;
  qed;
`;;

let AngleTrichotomy1 = theorem `;
  ∀α β. α <_ang β  ⇒  ¬(α ≡ β)

  proof
    intro_TAC ∀α β, H1;
    assume α ≡ β     [Con] by fol -;
    consider A O B G such that
    Angle α ∧ ¬Collinear A O B ∧ β = ∡ A O B ∧ G ∈ int_angle A O B ∧ α ≡ ∡ A O G     [H1'] by fol H1 AngleOrdering_DEF;
    ¬(A = O) ∧ ¬(O = B) ∧ ¬Collinear A O G     [Distinct] by fol H1' NonCollinearImpliesDistinct InteriorEZHelp;
    consider a such that
    Line a ∧ O ∈ a ∧ A ∈ a     [a_line] by fol Distinct I1;
    consider b such that
    Line b ∧ O ∈ b ∧ B ∈ b     [b_line] by fol Distinct I1;
    B ∉ a     [notBa] by fol a_line H1' Collinear_DEF ∉;
    G ∉ a ∧ G ∉ b ∧ G,B same_side a     [GintAOB] by fol a_line b_line H1' InteriorUse;
    ∡ A O G ≡ α     [] by fol H1' Distinct ANGLE C5Symmetric;
    ∡ A O G ≡ ∡ A O B     [] by fol H1' Distinct ANGLE - Con C5Transitive;
    ray O B = ray O G     [] by fol a_line Distinct notBa GintAOB - C4Uniqueness;
    G ∈ b     [] by fol Distinct - EndpointInRay b_line RayLine SUBSET;
    fol - GintAOB ∉;
  qed;
`;;

let AngleTrichotomy2 = theorem `;
  ∀α β γ.  α <_ang β  ∧  Angle γ  ∧  β ≡ γ  ⇒  α <_ang γ

  proof
    intro_TAC ∀α β γ, H1 H2 H3;
    consider A O B G such that
    Angle α ∧ ¬Collinear A O B ∧ β = ∡ A O B ∧ G ∈ int_angle A O B ∧ α ≡ ∡ A O G     [H1'] by fol H1 AngleOrdering_DEF;
    consider A' O' B' such that
    γ = ∡ A' O' B' ∧ ¬Collinear A' O' B'     [γA'O'B'] by fol H2 ANGLE;
    consider G' such that
    G' ∈ int_angle A' O' B' ∧ ∡ A O G ≡ ∡ A' O' G'     [G'intA'O'B'] by fol γA'O'B' H1' H3  OrderedCongruentAngles;
    ¬Collinear A O G ∧ ¬Collinear A' O' G'     [ncol] by fol H1' - InteriorEZHelp;
    α ≡ ∡ A' O' G'     [] by fol H1' ANGLE - G'intA'O'B' C5Transitive;
    fol H1' - ncol γA'O'B' G'intA'O'B' - AngleOrdering_DEF;
  qed;
`;;

let AngleOrderTransitivity = theorem `;
  ∀α β γ. α <_ang β  ∧  β <_ang γ  ⇒  α <_ang γ

  proof
    intro_TAC ∀α β γ, H1 H2;
    consider A O B G such that
    Angle β ∧ ¬Collinear A O B ∧ γ = ∡ A O B ∧ G ∈ int_angle A O B ∧ β ≡ ∡ A O G     [H2'] by fol H2 AngleOrdering_DEF;
    ¬Collinear A O G     [AOGncol] by fol H2'  InteriorEZHelp;
    Angle α ∧ Angle (∡ A O G)  ∧ Angle γ     [angles] by fol H1 AngleOrdering_DEF H2' - ANGLE;
    α <_ang ∡ A O G     [] by fol H1 H2' - AngleTrichotomy2;
    consider F such that
    F ∈ int_angle A O G ∧ α ≡ ∡ A O F     [FintAOG] by fol angles AOGncol - AngleOrderingUse;
    F ∈ int_angle A O B     [] by fol H2' - InteriorTransitivity;
    fol angles H2' - FintAOG AngleOrdering_DEF;
  qed;
`;;

let AngleTrichotomy = theorem `;
  ∀α β.  Angle α ∧ Angle β
   ⇒  (α ≡ β  ∨  α <_ang β  ∨  β <_ang α)  ∧
       ¬(α ≡ β  ∧  α <_ang β)  ∧
       ¬(α ≡ β  ∧  β <_ang α)  ∧
       ¬(α <_ang β  ∧  β <_ang α)

  proof
    intro_TAC ∀α β, H1;
    ¬(α ≡ β  ∧  α <_ang β)     [Not12] by fol AngleTrichotomy1;
    ¬(α ≡ β  ∧  β <_ang α)     [Not13] by fol H1 C5Symmetric AngleTrichotomy1;
    ¬(α <_ang β  ∧  β <_ang α)     [Not23] by fol H1 AngleOrderTransitivity AngleTrichotomy1 C5Reflexive;
    consider P O A such that
    α = ∡ P O A ∧ ¬Collinear P O A     [POA] by fol H1 ANGLE;
    ¬(P = O) ∧ ¬(O = A)      [Distinct] by fol - NonCollinearImpliesDistinct;
    consider a such that
    Line a ∧ O ∈ a ∧ A ∈ a     [a_line] by fol - I1;
    P ∉ a     [notPa] by fol - Distinct I1 POA Collinear_DEF ∉;
    ∃! r. Ray r ∧ ∃Q. ¬(O = Q) ∧ r = ray O Q ∧ Q ∉ a ∧ Q,P same_side a ∧ ∡ A O Q ≡ β     [] by simplify H1 Distinct a_line C4 -;
    consider Q such that
    ¬(O = Q) ∧ Q ∉ a ∧ Q,P same_side a ∧ ∡ A O Q ≡ β     [Qexists] by fol -;
    O ∉ Open (Q, P)     [notQOP] by fol a_line Qexists SameSide_DEF ∉;
    ¬Collinear A O P     [AOPncol] by fol POA CollinearSymmetry;
    ¬Collinear A O Q     [AOQncol] by fol a_line Distinct I1 Collinear_DEF Qexists ∉;
    Angle (∡ A O P) ∧ Angle (∡ A O Q)     [] by fol AOPncol - ANGLE;
    α ≡ ∡ A O P  ∧  β ≡ ∡ A O Q  ∧  ∡ A O P ≡ α     [flip] by fol H1 - POA AngleSymmetry C5Reflexive Qexists C5Symmetric;
    case_split QOPcol | QOPcolncol     by fol -;
    suppose Collinear Q O P;
      Collinear O P Q     [] by fol - CollinearSymmetry;
      Q ∈ ray O P ━ {O}     [] by fol Distinct - notQOP IN_Ray Qexists IN_DIFF IN_SING;
      ray O Q = ray O P     [] by fol Distinct - RayWellDefined;
      ∡ P O A = ∡ A O Q     [] by fol - Angle_DEF AngleSymmetry;
      fol - POA Qexists Not12 Not13 Not23;
    end;
    suppose ¬Collinear Q O P;
      P ∈ int_angle Q O A ∨ Q ∈ int_angle P O A     [] by fol Distinct a_line Qexists notPa - AngleOrdering;
      P ∈ int_angle A O Q ∨ Q ∈ int_angle A O P     [] by fol - InteriorAngleSymmetry;
      α <_ang ∡ A O Q  ∨  β <_ang ∡ A O P     [] by fol H1 AOQncol AOPncol - flip AngleOrdering_DEF;
      α <_ang β  ∨  β <_ang α     [] by fol H1 - Qexists flip AngleTrichotomy2;
      fol - Not12 Not13 Not23;
    end;
  qed;
`;;

let SupplementExists = theorem `;
  ∀α. Angle α  ⇒  ∃α'. α suppl α'

  proof
    intro_TAC ∀α, H1;
    consider A O B such that
    α = ∡ A O B ∧ ¬Collinear A O B ∧ ¬(A = O)     [def_α] by fol H1 ANGLE NonCollinearImpliesDistinct;
    consider A' such that
    O ∈ Open (A, A')     [AOA'] by fol - B2';
    ∡ A O B  suppl  ∡ A' O B     [AOBsup] by fol def_α - SupplementaryAngles_DEF AngleSymmetry;
    fol - def_α;
  qed;
`;;

let SupplementImpliesAngle = theorem `;
  ∀α β.  α suppl β  ⇒  Angle α ∧ Angle β

  proof
    intro_TAC ∀α β, H1;
    consider A O B A' such that
    ¬Collinear A O B  ∧  O ∈ Open (A, A')  ∧  α = ∡ A O B  ∧  β = ∡ B O A'     [H1'] by fol H1 SupplementaryAngles_DEF;
    ¬(O = A') ∧ Collinear A O A'     [Distinct] by fol - NonCollinearImpliesDistinct B1';
    ¬Collinear B O A'     [] by fol H1' CollinearSymmetry - NoncollinearityExtendsToLine;
    fol H1' - ANGLE;
  qed;
`;;

let RightImpliesAngle = theorem `;
  ∀α. Right α  ⇒  Angle α
  by fol RightAngle_DEF SupplementImpliesAngle`;;

let SupplementSymmetry = theorem `;
  ∀α β. α suppl β  ⇒  β suppl α

  proof
    intro_TAC ∀α β, H1;
  consider A O B A' such that
  ¬Collinear A O B  ∧  O ∈ Open (A, A')  ∧  α = ∡ A O B  ∧  β = ∡ B O A'     [H1'] by fol H1 SupplementaryAngles_DEF;
  ¬(O = A') ∧ Collinear A O A'     [] by fol - NonCollinearImpliesDistinct B1';
  ¬Collinear A' O B     [A'OBncol] by fol H1' CollinearSymmetry - NoncollinearityExtendsToLine;
  O ∈ Open (A', A)  ∧  β = ∡ A' O B  ∧  α = ∡ B O A     [] by fol H1' B1'  AngleSymmetry;
  fol A'OBncol - SupplementaryAngles_DEF;
  qed;
`;;

let SupplementsCongAnglesCong = theorem `;
  ∀α β α' β'.  α suppl α'  ∧  β suppl β'  ⇒  α ≡ β
    ⇒  α' ≡ β'

  proof
    intro_TAC ∀α β α' β', H1, H2;
    consider A O B A' such that
    ¬Collinear A O B  ∧  O ∈ Open (A, A')  ∧  α = ∡ A O B  ∧  α' = ∡ B O A'     [def_α] by fol H1 SupplementaryAngles_DEF;
    ¬(A = O) ∧ ¬(O = B) ∧ ¬(A = A') ∧ ¬(O = A') ∧ Collinear A O A'     [Distinctα] by fol - NonCollinearImpliesDistinct B1';
    ¬Collinear B A A' ∧ ¬Collinear O A' B     [BAA'ncol] by fol def_α CollinearSymmetry - NoncollinearityExtendsToLine;
    Segment (seg O A) ∧ Segment (seg O B) ∧ Segment (seg O A')     [Osegments] by fol Distinctα SEGMENT;
    consider C P D C' such that
    ¬Collinear C P D  ∧  P ∈ Open (C, C')  ∧  β = ∡ C P D  ∧  β' = ∡ D P C'     [def_β] by fol H1 SupplementaryAngles_DEF;
    ¬(C = P) ∧ ¬(P = D) ∧ ¬(P = C')     [Distinctβ] by fol def_β NonCollinearImpliesDistinct B1';
    consider X such that
    X ∈ ray P C ━ {P}  ∧  seg P X ≡ seg O A     [defX] by fol Osegments Distinctβ C1;
    consider Y such that
    Y ∈ ray P D ━ {P}  ∧  seg P Y ≡ seg O B  ∧  ¬(Y = P)     [defY] by fol Osegments Distinctβ C1 IN_DIFF IN_SING;
    consider X' such that
    X' ∈ ray P C' ━ {P}  ∧  seg P X' ≡ seg O A'     [defX'] by fol Osegments Distinctβ C1;
    P ∈ Open (X', C)  ∧  P ∈ Open (X, X')       [XPX'] by fol def_β - OppositeRaysIntersect1pointHelp defX;
    ¬(X = P) ∧ ¬(X' = P) ∧ Collinear X P X' ∧ ¬(X = X') ∧ ray A' O = ray A' A ∧ ray X' P = ray X' X     [XPX'line] by fol defX defX' IN_DIFF IN_SING - B1' def_α IntervalRay;
     Collinear P D Y ∧ Collinear P C X     [] by fol defY defX IN_DIFF IN_SING IN_Ray;
    ¬Collinear C P Y ∧ ¬Collinear X P Y     [XPYncol] by fol def_β - defY NoncollinearityExtendsToLine CollinearSymmetry XPX'line;
    ¬Collinear Y X X' ∧ ¬Collinear P X' Y     [YXX'ncol] by fol - CollinearSymmetry XPX' XPX'line NoncollinearityExtendsToLine;
    ray P X = ray P C  ∧  ray P Y = ray P D  ∧  ray P X' = ray P C'     [equalPrays] by fol Distinctβ defX defY defX' RayWellDefined;
    β = ∡ X P Y  ∧  β' = ∡ Y P X'  ∧  ∡ A O B ≡ ∡ X P Y     [AOBeqXPY] by fol def_β - Angle_DEF H2 def_α;
   seg O A ≡ seg P X  ∧  seg O B ≡ seg P Y  ∧  seg A' O ≡ seg X' P     [OAeq] by fol Osegments XPX'line SEGMENT defX defY defX' C2Symmetric SegmentSymmetry;
    seg A A' ≡ seg X X'     [AA'eq] by fol def_α XPX'line XPX' - SegmentSymmetry C3;
    A,O,B ≅ X,P,Y     [] by fol def_α XPYncol OAeq AOBeqXPY SAS;
    seg A B ≡ seg X Y  ∧  ∡ B A O ≡ ∡ Y X P     [AOB≅] by fol - TriangleCong_DEF AngleSymmetry;
    ray A O = ray A A'  ∧  ray X P = ray X  X'  ∧  ∡ B A A' ≡ ∡ Y X X'     [] by fol def_α XPX' IntervalRay - Angle_DEF;
    B,A,A' ≅ Y,X,X'     [] by fol BAA'ncol YXX'ncol AOB≅ - AA'eq - SAS;
    seg A' B ≡ seg X' Y  ∧  ∡ A A' B ≡ ∡ X X' Y     [] by fol - TriangleCong_DEF SegmentSymmetry;
    O,A',B ≅ P,X',Y     [] by fol BAA'ncol YXX'ncol OAeq - XPX'line Angle_DEF SAS;
    ∡ B O A' ≡ ∡ Y P X'     [] by fol - TriangleCong_DEF;
    fol - equalPrays def_β Angle_DEF def_α;
  qed;
`;;

let SupplementUnique = theorem `;
  ∀α β β'.  α suppl β  ∧   α suppl β'  ⇒  β ≡ β'
  by fol SupplementaryAngles_DEF ANGLE C5Reflexive SupplementsCongAnglesCong`;;

let CongRightImpliesRight = theorem `;
  ∀α β. Angle α  ∧  Right β  ⇒  α ≡ β  ⇒  Right α

  proof
    intro_TAC ∀α β, H1, H2;
    consider α' β' such that
    α suppl α'  ∧  β suppl β'  ∧  β ≡ β'     [suppl] by fol H1 SupplementExists H1 RightAngle_DEF;
    α' ≡ β'     [α'eqβ'] by fol suppl H2 SupplementsCongAnglesCong;
    Angle β ∧ Angle α' ∧ Angle β'     [] by fol suppl SupplementImpliesAngle;
    α ≡ α'     [] by fol     H1 - H2 suppl α'eqβ' C5Symmetric C5Transitive;
    fol suppl - RightAngle_DEF;
  qed;
`;;

let RightAnglesCongruentHelp = theorem `;
  ∀A O B A' P a.  ¬Collinear A O B  ∧  O ∈ Open (A, A')  ⇒
    Right (∡ A O B)  ∧  Right (∡ A O P)
    ⇒  P ∉ int_angle A O B

  proof
    intro_TAC ∀A O B A' P a, H1, H2;
    assume ¬(P ∉ int_angle A O B)     [Con] by fol -;
    P ∈ int_angle A O B     [PintAOB] by fol - ∉;
    B ∈ int_angle P O A'  ∧  B ∈ int_angle A' O P     [BintA'OP] by fol H1 - InteriorReflectionInterior InteriorAngleSymmetry ;
    ¬Collinear A O P ∧ ¬Collinear P O A'     [AOPncol] by fol PintAOB InteriorEZHelp - IN_InteriorAngle;
    ∡ A O B suppl ∡ B O A'  ∧  ∡ A O P suppl ∡ P O A'     [AOBsup] by fol H1 - SupplementaryAngles_DEF;
    consider α' β' such that
    ∡ A O B suppl α'  ∧  ∡ A O B ≡ α'  ∧  ∡ A O P suppl β'  ∧  ∡ A O P ≡ β'     [supplα'] by fol H2 RightAngle_DEF;
    α' ≡ ∡ B O A'  ∧  β' ≡ ∡ P O A'     [α'eqA'OB] by fol - AOBsup SupplementUnique;
    Angle (∡ A O B) ∧ Angle α' ∧ Angle (∡ B O A') ∧ Angle (∡ A O P) ∧ Angle β' ∧ Angle (∡ P O A')     [angles] by fol AOBsup supplα' SupplementImpliesAngle AngleSymmetry;
    ∡ A O B ≡ ∡ B O A'  ∧  ∡ A O P ≡ ∡ P O A'     [H2'] by fol - supplα' α'eqA'OB C5Transitive;
    ∡ A O P ≡ ∡ A O P  ∧  ∡ B O A' ≡ ∡ B O A'     [refl] by fol angles C5Reflexive;
    ∡ A O P <_ang ∡ A O B  ∧  ∡ B O A' <_ang ∡ P O A'     [BOA'lessPOA'] by fol angles H1 PintAOB - AngleOrdering_DEF AOPncol CollinearSymmetry BintA'OP AngleSymmetry;
    ∡ A O P <_ang ∡ B O A'     [] by fol - angles H2' AngleTrichotomy2;
    ∡ A O P <_ang ∡ P O A'     [] by fol - BOA'lessPOA' AngleOrderTransitivity;
    fol - H2' AngleTrichotomy1;
  qed;
`;;

let RightAnglesCongruent = theorem `;
  ∀α β. Right α ∧ Right β  ⇒  α ≡ β

  proof
    intro_TAC ∀α β, H1;
    consider α' such that
    α suppl α'  ∧  α ≡ α'     [αright] by fol H1 RightAngle_DEF;
    consider A O B A' such that
    ¬Collinear A O B  ∧  O ∈ Open (A, A')  ∧  α = ∡ A O B  ∧  α' = ∡ B O A'     [def_α] by fol - SupplementaryAngles_DEF;
    ¬(A = O) ∧ ¬(O = B)     [Distinct] by fol def_α NonCollinearImpliesDistinct B1';
    consider a such that
    Line a ∧ O ∈ a ∧ A ∈ a     [a_line] by fol Distinct I1;
    B ∉ a     [notBa] by fol - def_α Collinear_DEF ∉;
    Angle β     [] by fol H1 RightImpliesAngle;
    ∃! r. Ray r ∧ ∃P. ¬(O = P) ∧ r = ray O P ∧ P ∉ a ∧ P,B same_side a ∧ ∡ A O P ≡ β     [] by simplify C4 - Distinct a_line notBa;
    consider P such that
    ¬(O = P) ∧ P ∉ a ∧ P,B same_side a ∧ ∡ A O P ≡ β     [defP] by fol -;
    O ∉ Open (P, B)     [notPOB] by fol a_line - SameSide_DEF ∉;
    ¬Collinear A O P     [AOPncol] by fol a_line Distinct defP NonCollinearRaa CollinearSymmetry;
    Right (∡ A O P)     [AOPright] by fol - ANGLE H1 defP CongRightImpliesRight;
    P ∉ int_angle A O B  ∧  B ∉ int_angle A O P     [] by fol def_α H1 - AOPncol AOPright RightAnglesCongruentHelp;
    Collinear P O B     [] by fol Distinct a_line defP notBa - AngleOrdering InteriorAngleSymmetry ∉;
    P ∈ ray O B ━ {O}     [] by fol Distinct - CollinearSymmetry notPOB IN_Ray defP IN_DIFF IN_SING;
    ray O P = ray O B  ∧  ∡ A O P = ∡ A O B     [] by fol Distinct - RayWellDefined Angle_DEF;
    fol - defP def_α;
  qed;
`;;

let OppositeRightAnglesLinear = theorem `;
  ∀A B O H h.  ¬Collinear A O H ∧ ¬Collinear H O B  ⇒
    Right (∡ A O H) ∧ Right (∡ H O B)  ⇒
    Line h ∧ O ∈ h ∧ H ∈ h  ∧  ¬(A,B same_side h)
    ⇒  O ∈ Open (A, B)

  proof
    intro_TAC ∀A B O H h, H0, H1, H2;
    ¬(A = O) ∧ ¬(O = H) ∧ ¬(O = B)     [Distinct] by fol  H0 NonCollinearImpliesDistinct;
    A ∉ h ∧ B ∉ h     [notABh] by fol H0 H2 Collinear_DEF ∉;
    consider E such that
    O ∈ Open (A, E) ∧ ¬(E = O)     [AOE] by fol Distinct B2' B1';
    ∡ A O H  suppl  ∡ H O E     [AOHsupplHOE] by fol H0 - SupplementaryAngles_DEF;
    E ∉ h     [notEh] by fol H2 ∉ AOE BetweenLinear notABh;
    ¬(A,E same_side  h)     [] by fol H2 AOE SameSide_DEF;
    B,E same_side  h     [Bsim_hE] by fol H2 notABh notEh - H2 AtMost2Sides;
    consider α' such that
    ∡ A O H  suppl  α'  ∧  ∡ A O H ≡ α'     [AOHsupplα'] by fol H1 RightAngle_DEF;
    Angle (∡ H O B) ∧ Angle (∡ A O H) ∧ Angle α' ∧ Angle (∡ H O E)     [angα'] by fol H1 RightImpliesAngle - AOHsupplHOE SupplementImpliesAngle;
    ∡ H O B ≡ ∡ A O H  ∧  α' ≡ ∡ H O E     [] by fol H1 RightAnglesCongruent AOHsupplα' AOHsupplHOE SupplementUnique;
    ∡ H O B ≡ ∡ H O E     [] by fol angα' - AOHsupplα' C5Transitive;
    ray O B = ray O E     [] by fol H2 Distinct notABh notEh Bsim_hE - C4Uniqueness;
    B ∈ ray O E ━ {O}     [] by fol Distinct EndpointInRay - IN_DIFF IN_SING;
    fol AOE - OppositeRaysIntersect1pointHelp B1';
  qed;
`;;

let RightImpliesSupplRight = theorem `;
  ∀A O B A'.  ¬Collinear A O B  ∧  O ∈ Open (A, A')  ∧  Right (∡ A O B)
    ⇒  Right (∡ B O A')

  proof
    intro_TAC ∀A O B A', H1 H2 H3;
    ∡ A O B suppl ∡ B O A'  ∧  Angle (∡ A O B)  ∧  Angle (∡ B O A')     [AOBsuppl] by fol H1 H2 SupplementaryAngles_DEF SupplementImpliesAngle;
    consider β such that
    ∡ A O B suppl β ∧ ∡ A O B ≡ β     [βsuppl] by fol H3 RightAngle_DEF;
    Angle β  ∧  β ≡ ∡ A O B     [angβ] by fol - SupplementImpliesAngle C5Symmetric;
    ∡ B O A' ≡ β     [] by fol AOBsuppl βsuppl SupplementUnique;
    ∡ B O A' ≡ ∡ A O B     [] by fol AOBsuppl angβ - βsuppl C5Transitive;
    fol AOBsuppl H3 - CongRightImpliesRight;
  qed;
`;;

let IsoscelesCongBaseAngles = theorem `;
  ∀A B C.  ¬Collinear A B C  ∧  seg B A ≡ seg B C  ⇒   ∡ C A B  ≡ ∡ A C B

  proof
    intro_TAC ∀A B C, H1 H2;
    ¬(A = B) ∧ ¬(B = C) ∧ ¬Collinear C B A     [CBAncol] by fol H1 NonCollinearImpliesDistinct CollinearSymmetry;
    seg B C ≡ seg B A  ∧  ∡ A B C ≡ ∡ C B A     [] by fol - SEGMENT H2 C2Symmetric H1 ANGLE AngleSymmetry C5Reflexive;
    fol H1 CBAncol H2 - SAS TriangleCong_DEF;
  qed;
`;;

let C4withC1 = theorem `;
  ∀α l O A Y P Q.  Angle α ∧ ¬(O = A) ∧ ¬(P = Q)  ⇒
    Line l ∧ O ∈ l ∧ A ∈ l ∧ Y ∉ l  ⇒
    ∃N. ¬(O = N) ∧ N ∉ l ∧ N,Y same_side l ∧ seg O N ≡ seg P Q ∧ ∡ A O N ≡ α

  proof
    intro_TAC ∀α l O A Y P Q, H1, l_line;
    ∃! r. Ray r ∧ ∃B. ¬(O = B) ∧ r = ray O B ∧ B ∉ l ∧ B,Y same_side l ∧ ∡ A O B ≡ α     [] by simplify C4 H1 l_line;
    consider B such that
    ¬(O = B) ∧ B ∉ l ∧ B,Y same_side l ∧ ∡ A O B ≡ α     [Bexists] by fol -;
    consider N such that
    N ∈ ray O B ━ {O}  ∧  seg O N ≡ seg P Q     [Nexists] by fol H1 - SEGMENT C1;
    N ∉ l ∧ N,B same_side l     [notNl] by fol l_line Bexists Nexists RaySameSide;
    N,Y same_side l     [Nsim_lY] by fol l_line - Bexists SameSideTransitive;
    ray O N = ray O B     [] by fol Bexists Nexists RayWellDefined;
    ∡ A O N ≡ α     [] by fol - Bexists Angle_DEF;
    fol Nexists IN_DIFF IN_SING notNl Nsim_lY Nexists -;
  qed;
`;;

let C4OppositeSide = theorem `;
  ∀α l O A Z P Q.  Angle α ∧ ¬(O = A) ∧ ¬(P = Q)  ⇒
    Line l ∧ O ∈ l ∧ A ∈ l ∧ Z ∉ l
    ⇒  ∃N. ¬(O = N) ∧ N ∉ l ∧ ¬(Z,N same_side l) ∧
    seg O N ≡ seg P Q ∧ ∡ A O N ≡ α

  proof
    intro_TAC ∀α l O A Z P Q, H1, l_line;
    ¬(Z = O)     [] by fol l_line ∉;
    consider Y such that
    O ∈ Open (Z, Y)     [ZOY] by fol - B2';
    ¬(O = Y) ∧ Collinear O Z Y     [notOY] by fol - B1' CollinearSymmetry;
    Y ∉ l     [notYl] by fol notOY l_line NonCollinearRaa ∉;
    consider N such that
    ¬(O = N) ∧ N ∉ l  ∧  N,Y same_side l  ∧ seg O N ≡ seg P Q  ∧  ∡ A O N ≡ α     [Nexists] by simplify C4withC1 H1 l_line -;
    ¬(Z,Y same_side l)     [] by fol l_line ZOY SameSide_DEF;
    ¬(Z,N same_side l)     [] by fol l_line Nexists notYl - SameSideTransitive;
    fol - Nexists;
  qed;
`;;

let SSS = theorem `;
  ∀A B C A' B' C'.  ¬Collinear A B C ∧ ¬Collinear A' B' C'  ⇒
    seg A B ≡ seg A' B'  ∧  seg A C ≡ seg A' C'  ∧  seg B C ≡ seg B' C'
    ⇒  A,B,C ≅ A',B',C'

  proof
    intro_TAC ∀A B C A' B' C', H1, H2;
    ¬(A = B) ∧ ¬(A = C) ∧ ¬(B = C) ∧ ¬(A' = B') ∧ ¬(B' = C')     [Distinct] by fol H1 NonCollinearImpliesDistinct;
    consider h such that
    Line h ∧ A ∈ h ∧ C ∈ h     [h_line] by fol Distinct I1;
    B ∉ h     [notBh] by fol h_line H1 ∉ Collinear_DEF;
    Segment (seg A B) ∧ Segment (seg C B) ∧ Segment (seg A' B') ∧ Segment (seg C' B')     [segments] by fol Distinct - SEGMENT;
    Angle (∡ C' A' B')     [] by fol H1 CollinearSymmetry ANGLE;
    consider N such that
    ¬(A = N) ∧ N ∉ h ∧ ¬(B,N same_side h) ∧ seg A N ≡ seg A' B'  ∧  ∡ C A N ≡ ∡ C' A' B'     [Nexists] by simplify C4OppositeSide - Distinct h_line notBh;
    ¬(C = N)     [] by fol h_line Nexists ∉;
    Segment (seg A N) ∧ Segment (seg C N)     [segN] by fol Nexists - SEGMENT;
    ¬Collinear A N C     [ANCncol] by fol Distinct h_line Nexists NonCollinearRaa;
    Angle (∡ A B C) ∧ Angle (∡ A' B' C') ∧ Angle (∡ A N C)     [angles] by fol H1 - ANGLE;
    seg A B ≡ seg A N     [ABeqAN] by fol segments segN Nexists H2 C2Symmetric C2Transitive;
    C,A,N ≅ C',A',B'     [] by fol ANCncol H1 CollinearSymmetry H2 Nexists SAS;
    ∡ A N C ≡ ∡ A' B' C'  ∧  seg C N ≡ seg C' B'     [ANCeq] by fol - TriangleCong_DEF;
    seg C B ≡ seg C N     [CBeqCN] by fol segments segN - H2 SegmentSymmetry C2Symmetric C2Transitive;
    consider G such that
    G ∈ h ∧ G ∈ Open (B, N)     [BGN] by fol Nexists h_line SameSide_DEF;
    ¬(B = N)     [notBN] by fol - B1';
    ray B G = ray B N  ∧  ray N G = ray N B     [Grays] by fol BGN B1' IntervalRay;
    consider v such that
    Line v ∧ B ∈ v ∧ N ∈ v     [v_line] by fol notBN I1;
    G ∈ v ∧ ¬(h = v)     [] by fol v_line BGN BetweenLinear notBh ∉;
    h ∩ v = {G}     [hvG] by fol h_line v_line - BGN I1Uniqueness;
    ¬(G = A)  ⇒  ∡ A B G ≡ ∡ A N G     [ABGeqANG]
    proof
      intro_TAC notGA;
      A ∉ v     [] by fol hvG h_line - EquivIntersectionHelp IN_DIFF IN_SING;
      ¬Collinear B A N     [] by fol v_line notBN I1 Collinear_DEF - ∉;
      ∡ N B A ≡ ∡ B N A     [] by fol - ABeqAN IsoscelesCongBaseAngles;
      ∡ G B A ≡ ∡ G N A     [] by fol - Grays Angle_DEF notGA;
      fol - AngleSymmetry;
    qed;
    ¬(G = C)  ⇒  ∡ G B C ≡ ∡ G N C     [GBCeqGNC]
    proof
      intro_TAC notGC;
      C ∉ v     [] by fol hvG h_line - EquivIntersectionHelp IN_DIFF IN_SING;
      ¬Collinear B C N     [] by fol v_line notBN I1 Collinear_DEF - ∉;
      ∡ N B C ≡ ∡ B N C     [] by fol - CBeqCN IsoscelesCongBaseAngles AngleSymmetry;
      fol - Grays Angle_DEF;
    qed;
    ∡ A B C ≡ ∡ A N C     []
    proof
      assume ¬(G = A) ∧ ¬(G = C) [AGCdistinct] by fol - Distinct GBCeqGNC ABGeqANG;
      ∡ A B G ≡ ∡ A N G  ∧  ∡ G B C ≡ ∡ G N C     [Gequivs] by fol - ABGeqANG GBCeqGNC;
      ¬Collinear G B C ∧ ¬Collinear G N C ∧ ¬Collinear G B A ∧ ¬Collinear G N A     [Gncols] by fol AGCdistinct h_line BGN notBh Nexists NonCollinearRaa;
      Collinear A G C     [] by fol h_line BGN Collinear_DEF;
      G ∈ Open (A, C) ∨ C ∈ Open (G, A) ∨ A ∈ Open (C, G)     [] by fol Distinct AGCdistinct - B3';
      case_split AGC | GAC | CAG     by fol -;
      suppose G ∈ Open (A, C);
        G ∈ int_angle A B C  ∧  G ∈ int_angle A N C     [] by fol H1 ANCncol - ConverseCrossbar;
        fol - Gequivs AngleAddition;
      end;
      suppose C ∈ Open (G, A);
        C ∈ int_angle G B A  ∧  C ∈ int_angle G N A     [] by fol Gncols - B1' ConverseCrossbar;
        fol - Gequivs AngleSubtraction AngleSymmetry;
      end;
      suppose A ∈ Open (C, G);
        A ∈ int_angle G B C  ∧  A ∈ int_angle G N C     [] by fol Gncols - B1' ConverseCrossbar;
        fol - Gequivs AngleSymmetry AngleSubtraction;
      end;
    qed;
    ∡ A B C ≡ ∡ A' B' C'     [] by fol angles - ANCeq C5Transitive;
    fol H1 H2 SegmentSymmetry - SAS;
  qed;
`;;

let AngleBisector = theorem `;
  ∀A B C. ¬Collinear B A C  ⇒  ∃M. M ∈ int_angle B A C  ∧  ∡ B A M ≡ ∡ M A C

  proof
    intro_TAC ∀A B C, H1;
    ¬(A = B) ∧ ¬(A = C)     [Distinct] by fol H1 NonCollinearImpliesDistinct;
    consider D such that
    B ∈ Open (A, D)     [ABD] by fol Distinct B2';
    ¬(A = D) ∧ Collinear A B D ∧ Segment (seg A D)     [ABD'] by fol - B1' SEGMENT;
    consider E such that
    E ∈ ray A C ━ {A}  ∧  seg A E ≡ seg A D  ∧  ¬(A = E)     [ErAC] by fol - Distinct C1 IN_Ray IN_DIFF IN_SING;
    Collinear A C E  ∧  D ∈ ray A B ━ {A}     [notAE] by fol - IN_Ray ABD IntervalRayEZ IN_DIFF IN_SING;
    ray A D = ray A B  ∧  ray A E =  ray A C     [equalrays] by fol Distinct notAE ErAC RayWellDefined;
    ¬Collinear D A E ∧ ¬Collinear E A D ∧ ¬Collinear A E D     [EADncol] by fol H1 ABD' notAE ErAC CollinearSymmetry NoncollinearityExtendsToLine;
    ∡ D E A ≡ ∡ E D A     [DEAeq] by fol EADncol ErAC IsoscelesCongBaseAngles;
    ¬Collinear E D A ∧ Angle (∡ E D A) ∧ ¬Collinear A D E ∧ ¬Collinear D E A     [angEDA] by fol EADncol CollinearSymmetry ANGLE;
    ¬(D = E)     [notDE] by fol EADncol NonCollinearImpliesDistinct;
    consider h such that
    Line h ∧ D ∈ h ∧ E ∈ h     [h_line] by fol - I1;
    A ∉ h     [notAh] by fol - Collinear_DEF EADncol ∉;
    consider M such that
    ¬(D = M)  ∧  M ∉ h  ∧  ¬(A,M same_side h)  ∧  seg D M ≡ seg D A  ∧  ∡ E D M ≡ ∡ E D A     [Mexists] by simplify C4OppositeSide angEDA notDE ABD' h_line -;
    ¬(A = M)     [notAM] by fol h_line - SameSideReflexive;
    ¬Collinear E D M ∧ ¬Collinear D E M ∧ ¬Collinear M E D     [EDMncol] by fol  notDE h_line Mexists NonCollinearRaa CollinearSymmetry;
    seg D E ≡ seg D E  ∧  seg M A ≡ seg M A     [MArefl] by fol notDE notAM SEGMENT C2Reflexive;
    E,D,M ≅ E,D,A     [] by fol EDMncol angEDA - Mexists SAS;
    seg M E ≡ seg A E ∧ ∡ M E D ≡ ∡ A E D ∧ ∡ D E M ≡ ∡ D E A     [MED≅] by fol - TriangleCong_DEF SegmentSymmetry AngleSymmetry;
    ∡ E D A ≡ ∡ D E A  ∧  ∡ E D A ≡ ∡ E D M  ∧  ∡ D E A ≡ ∡ D E M     [EDAeqEDM] by fol EDMncol ANGLE angEDA Mexists MED≅ DEAeq C5Symmetric;
    consider G such that
    G ∈ h ∧ G ∈ Open (A, M)     [AGM] by fol Mexists h_line SameSide_DEF;
    M ∈ ray A G ━ {A}     [MrAG] by fol - IntervalRayEZ;
    consider v such that
    Line v ∧ A ∈ v ∧ M ∈ v ∧ G ∈ v     [v_line] by fol notAM I1 AGM BetweenLinear;
    ¬(v = h)  ∧  v ∩ h = {G}     [vhG] by fol - notAh ∉ h_line AGM I1Uniqueness;
    D ∉ v     [notDv]
    proof
      assume ¬(D ∉ v)     [Con] by fol -;
      D ∈ v  ∧  D = G     [DG] by fol h_line - ∉ vhG IN_INTER IN_SING;
      D ∈ Open (A, M)     [] by fol DG AGM;
      ∡ E D A suppl ∡ E D M     [EDAsuppl] by fol angEDA - SupplementaryAngles_DEF AngleSymmetry;
      Right (∡ E D A)     [] by fol EDAsuppl EDAeqEDM RightAngle_DEF;
      Right (∡ A E D)     [RightAED] by fol angEDA ANGLE - DEAeq CongRightImpliesRight AngleSymmetry;
      Right (∡ D E M)     [] by fol EDMncol ANGLE - MED≅ CongRightImpliesRight AngleSymmetry;
      E ∈ Open (A, M)     [] by fol EADncol EDMncol RightAED - h_line Mexists  OppositeRightAnglesLinear;
      E ∈ v  ∧  E = G     [] by fol v_line - BetweenLinear h_line vhG IN_INTER IN_SING;
      fol - DG notDE;
    qed;
    E ∉ v     [notEv]
    proof
      assume ¬(E ∉ v)     [Con] by fol -;
      E ∈ v  ∧  E = G     [EG] by fol h_line - ∉ vhG IN_INTER IN_SING;
      E ∈ Open (A, M)     [] by fol - AGM;
      ∡ D E A suppl ∡ D E M     [DEAsuppl] by fol EADncol - SupplementaryAngles_DEF AngleSymmetry;
      Right (∡ D E A)     [RightDEA] by fol DEAsuppl EDAeqEDM RightAngle_DEF;
      Right (∡ E D A)     [RightEDA] by fol angEDA RightDEA EDAeqEDM CongRightImpliesRight;
      Right (∡ E D M)     [] by fol EDMncol ANGLE RightEDA Mexists CongRightImpliesRight;
      D ∈ Open (A, M)     [] by fol angEDA EDMncol RightEDA AngleSymmetry - h_line Mexists  OppositeRightAnglesLinear;
      D ∈ v ∧ D = G     [] by fol v_line - BetweenLinear h_line vhG IN_INTER IN_SING;
      fol - EG notDE;
    qed;
    ¬Collinear M A E ∧ ¬Collinear M A D  ∧  ¬(M = E)     [MAEncol] by fol notAM v_line notEv notDv NonCollinearRaa CollinearSymmetry NonCollinearImpliesDistinct;
    seg M E ≡ seg A D     [MEeqAD] by fol - ErAC ABD' SEGMENT MED≅ ErAC C2Transitive;
    seg A D ≡ seg M D     [] by fol SegmentSymmetry ABD' Mexists SEGMENT C2Symmetric;
    seg M E ≡ seg M D     [] by fol MAEncol ABD' Mexists SEGMENT MEeqAD - C2Transitive;
    M,A,E ≅ M,A,D     [] by fol MAEncol MArefl - ErAC SSS;
    ∡ M A E ≡ ∡ M A D     [MAEeq] by fol - TriangleCong_DEF;
    ∡ D A M ≡ ∡ M A E     [] by fol MAEncol ANGLE MAEeq C5Symmetric AngleSymmetry;
    ∡ B A M ≡ ∡ M A C     [BAMeqMAC] by fol - equalrays Angle_DEF;
    ¬(E,D same_side v)     []
    proof
      assume E,D same_side v     [Con] by fol -;
      ray A D = ray A E     [] by fol v_line notAM notDv notEv - MAEeq C4Uniqueness;
      fol ABD' EndpointInRay - IN_Ray EADncol;
    qed;
    consider H such that
    H ∈ v ∧ H ∈ Open (E, D)     [EHD] by fol v_line - SameSide_DEF;
    H = G     [] by fol - h_line BetweenLinear IN_INTER vhG IN_SING;
    G ∈ int_angle E A D     [GintEAD] by fol EADncol  - EHD ConverseCrossbar;
    M ∈ int_angle E A D     [MintEAD] by fol GintEAD MrAG WholeRayInterior;
    B ∈ ray A D ━ {A}   ∧   C ∈ ray A E ━ {A}     [] by fol equalrays Distinct EndpointInRay IN_DIFF IN_SING;
    M ∈ int_angle B A C     [] by fol MintEAD - InteriorWellDefined InteriorAngleSymmetry;
    fol - BAMeqMAC;
  qed;
`;;

let EuclidPropositionI_6 = theorem `;
  ∀A B C. ¬Collinear A B C  ∧  ∡ B A C ≡ ∡ B C A  ⇒  seg B A ≡ seg B C

  proof
    intro_TAC ∀A B C, H1 H2;
    ¬(A = C)     [] by fol H1 NonCollinearImpliesDistinct;
    seg C A ≡ seg A C     [CAeqAC] by fol SegmentSymmetry - SEGMENT C2Reflexive;
    ¬Collinear B C A ∧ ¬Collinear C B A ∧ ¬Collinear B A C     [BCAncol] by fol H1 CollinearSymmetry;
    ∡ A C B ≡ ∡ C A B     [] by fol - ANGLE H2 C5Symmetric AngleSymmetry;
    C,B,A ≅ A,B,C     [] by fol H1 BCAncol CAeqAC H2 - ASA;
    fol - TriangleCong_DEF;
  qed;
`;;

let IsoscelesExists = theorem `;
  ∀A B. ¬(A = B)  ⇒  ∃D. ¬Collinear A D B  ∧  seg D A ≡ seg D B

  proof
    intro_TAC ∀A B, H1;
    consider l such that
    Line l ∧ A ∈ l ∧ B ∈ l     [l_line] by fol H1 I1;
    consider C such that
    C ∉ l     [notCl] by fol - ExistsPointOffLine;
    ¬Collinear C A B ∧ ¬Collinear C B A ∧ ¬Collinear A B C ∧ ¬Collinear A C B ∧ ¬Collinear B A C     [CABncol] by fol l_line H1 I1 Collinear_DEF - ∉;
    ∡ C A B ≡ ∡ C B A  ∨  ∡ C A B <_ang ∡ C B A  ∨  ∡ C B A <_ang ∡ C A B     [] by fol - ANGLE AngleTrichotomy;
    case_split cong | less | greater     by fol -;
    suppose ∡ C A B ≡ ∡ C B A;
      fol - CABncol EuclidPropositionI_6;
    end;
    suppose ∡ C A B <_ang ∡ C B A;
      ∡ C A B <_ang ∡ A B C     [] by fol - AngleSymmetry;
      consider E such that
      E ∈ int_angle A B C  ∧  ∡ C A B ≡ ∡ A B E     [Eexists] by fol CABncol ANGLE - AngleOrderingUse;
      ¬(B = E)     [notBE] by fol - InteriorEZHelp;
      consider D such that
      D ∈ Open (A, C)  ∧  D ∈ ray B E ━ {B}     [Dexists] by fol Eexists Crossbar_THM;
      D ∈ int_angle A B C     [] by fol Eexists - WholeRayInterior;
      ¬Collinear A D B     [ADBncol] by fol - InteriorEZHelp CollinearSymmetry;
      ray B D = ray B E  ∧  ray A D = ray A C     [] by fol notBE Dexists RayWellDefined IntervalRay;
      ∡ D A B ≡ ∡ A B D     [] by fol Eexists - Angle_DEF;
      fol ADBncol - AngleSymmetry EuclidPropositionI_6;
    end;
    suppose ∡ C B A <_ang ∡ C A B;
      ∡ C B A <_ang ∡ B A C     [] by fol - AngleSymmetry;
      consider E such that
      E ∈ int_angle B A C  ∧  ∡ C B A ≡ ∡ B A E     [Eexists] by fol CABncol ANGLE - AngleOrderingUse;
      ¬(A = E)     [notAE] by fol - InteriorEZHelp;
      consider D such that
      D ∈ Open (B, C) ∧ D ∈ ray A E ━ {A}     [Dexists] by fol Eexists Crossbar_THM;
      D ∈ int_angle B A C     [] by fol Eexists - WholeRayInterior;
      ¬Collinear A D B ∧ ¬Collinear D A B ∧ ¬Collinear D B A     [ADBncol] by fol - InteriorEZHelp CollinearSymmetry;
      ray A D = ray A E  ∧  ray B D = ray B C     [] by fol notAE Dexists RayWellDefined IntervalRay;
      ∡ D B A ≡ ∡ B A D     [] by fol Eexists - Angle_DEF;
      ∡ D A B ≡ ∡ D B A     [] by fol AngleSymmetry  ADBncol ANGLE - C5Symmetric;
      fol ADBncol - EuclidPropositionI_6;
    end;
  qed;
`;;

let MidpointExists = theorem `;
  ∀A B. ¬(A = B)  ⇒  ∃M. M ∈ Open (A, B)  ∧  seg A M ≡ seg M B

  proof
    intro_TAC ∀A B, H1;
    consider D such that
    ¬Collinear A D B  ∧  seg D A ≡ seg D B     [Dexists] by fol H1 IsoscelesExists;
    consider F such that
    F ∈ int_angle A D B  ∧  ∡ A D F ≡ ∡ F D B     [Fexists] by fol - AngleBisector;
    ¬(D = F)     [notDF] by fol - InteriorEZHelp;
    consider M such that
    M ∈ Open (A, B) ∧  M ∈ ray D F ━ {D}     [Mexists] by fol Fexists Crossbar_THM;
    ray D M = ray D F     [] by fol notDF - RayWellDefined;
    ∡ A D M ≡ ∡ M D B     [ADMeqMDB] by fol Fexists - Angle_DEF;
    M ∈ int_angle A D B     [] by fol Fexists Mexists WholeRayInterior;
    ¬(D = M) ∧ ¬Collinear A D M ∧ ¬Collinear B D M     [ADMncol] by fol - InteriorEZHelp InteriorAngleSymmetry;
    seg D M ≡ seg D M     [] by fol - SEGMENT C2Reflexive;
    A,D,M ≅ B,D,M     [] by fol ADMncol Dexists - ADMeqMDB AngleSymmetry SAS;
    fol Mexists - TriangleCong_DEF SegmentSymmetry;
  qed;
`;;

let EuclidPropositionI_7short = theorem `;
  ∀A B C D a.  ¬(A = B) ∧ Line a ∧ A ∈ a ∧ B ∈ a  ⇒
    ¬(C = D) ∧ C ∉ a ∧ D ∉ a ∧ C,D same_side a  ⇒  seg A C ≡ seg A D
    ⇒  ¬(seg B C ≡ seg B D)

  proof
    intro_TAC ∀A B C D a, a_line, Csim_aD, ACeqAD;
    ¬(A = C) ∧ ¬(A = D)     [AnotCD] by fol a_line Csim_aD ∉;
    assume seg B C ≡ seg B D     [Con] by fol -;
    seg C B ≡ seg D B  ∧  seg A B ≡ seg A B  ∧  seg A D ≡ seg A D     [segeqs] by fol - SegmentSymmetry a_line AnotCD SEGMENT C2Reflexive;
    ¬Collinear A C B  ∧ ¬Collinear A D B     [] by fol a_line I1 Csim_aD Collinear_DEF ∉;
    A,C,B ≅ A,D,B     [] by fol - ACeqAD segeqs SSS;
    ∡ B A C ≡ ∡ B A D     [] by fol - TriangleCong_DEF;
    ray A D = ray A C     [] by fol a_line Csim_aD - C4Uniqueness;
    C ∈ ray A D ━ {A}  ∧  D ∈ ray A D ━ {A}     [] by fol AnotCD - EndpointInRay IN_DIFF IN_SING;
    C = D     [] by fol AnotCD SEGMENT - ACeqAD segeqs C1;
    fol - Csim_aD;
  qed;
`;;

let EuclidPropositionI_7Help = theorem `;
  ∀A B C D a.  ¬(A = B)  ⇒  Line a ∧ A ∈ a ∧ B ∈ a  ⇒
    ¬(C = D) ∧ C ∉ a ∧ D ∉ a ∧ C,D same_side a  ⇒  seg A C ≡ seg A D  ⇒
    C ∈ int_triangle D A B  ∨  ConvexQuadrilateral A B C D
    ⇒  ¬(seg B C ≡ seg B D)

  proof
    intro_TAC ∀A B C D a, notAB, a_line, Csim_aD, ACeqAD, Int_ConvQuad;
    ¬(A = C) ∧ ¬(A = D) ∧ ¬(B = C) ∧ ¬(B = D)     [Distinct] by fol a_line Csim_aD ∉ SameSide_DEF;
    case_split convex | CintDAB     by fol Int_ConvQuad;
    suppose ConvexQuadrilateral A B C D;
      A ∈ int_angle B C D  ∧  B ∈ int_angle C D A  ∧  Tetralateral A B C D     [ABint] by fol - ConvexQuad_DEF Quadrilateral_DEF;
      ¬Collinear B C D ∧ ¬Collinear D C B ∧ ¬Collinear C B D ∧ ¬Collinear C D A ∧ ¬Collinear D A C ∧ Angle (∡ D C A) ∧ Angle (∡ C D B)     [angCDB] by fol - Tetralateral_DEF CollinearSymmetry ANGLE;
      ∡ C D A ≡ ∡ D C A     [CDAeqDCA] by fol angCDB Distinct SEGMENT ACeqAD C2Symmetric IsoscelesCongBaseAngles;
      A ∈ int_angle D C B  ∧  ∡ D C A ≡ ∡ D C A  ∧  ∡ C D B ≡ ∡ C D B     [] by fol ABint InteriorAngleSymmetry angCDB ANGLE C5Reflexive;
      ∡ D C A <_ang ∡ D C B  ∧  ∡ C D B <_ang ∡ C D A     [] by fol angCDB ABint - AngleOrdering_DEF;
      ∡ C D B <_ang ∡ D C B     [] by fol - angCDB CDAeqDCA AngleTrichotomy2 AngleOrderTransitivity;
      ¬(∡ D C B ≡ ∡ C D B)     [] by fol - AngleTrichotomy1 angCDB ANGLE C5Symmetric;
      fol angCDB - IsoscelesCongBaseAngles;
    end;
    suppose C ∈ int_triangle D A B;
      C ∈ int_angle A D B  ∧  C ∈ int_angle D A B     [CintADB] by fol - IN_InteriorTriangle InteriorAngleSymmetry;
      ¬Collinear A D C ∧ ¬Collinear B D C     [ADCncol] by fol CintADB InteriorEZHelp InteriorAngleSymmetry;
      ¬Collinear D A C ∧ ¬Collinear C D A ∧ ¬Collinear A C D ∧ ¬Collinear A D C     [DACncol] by fol - CollinearSymmetry;
      ¬Collinear B C D ∧ Angle (∡ D C A) ∧ Angle (∡ C D B) ∧ ¬Collinear D C B     [angCDB] by fol ADCncol - CollinearSymmetry ANGLE;
      ∡ C D A ≡ ∡ D C A     [CDAeqDCA] by fol DACncol Distinct ADCncol SEGMENT ACeqAD C2Symmetric IsoscelesCongBaseAngles;
      consider E such that
      D ∈ Open (A, E) ∧ ¬(D = E) ∧ Collinear A D E     [ADE] by fol Distinct B2' B1';
      B ∈ int_angle C D E ∧ Collinear D A E     [BintCDE] by fol CintADB - InteriorReflectionInterior CollinearSymmetry;
      ¬Collinear C D E     [CDEncol] by fol DACncol - ADE NoncollinearityExtendsToLine;
      consider F such that
      F ∈ Open (B, D)  ∧  F ∈ ray A C ━ {A}     [Fexists] by fol CintADB Crossbar_THM B1';
      F ∈ int_angle B C D     [FintBCD] by fol ADCncol CollinearSymmetry - ConverseCrossbar;
      ¬Collinear D C F     [DCFncol] by fol Distinct ADCncol CollinearSymmetry Fexists B1' NoncollinearityExtendsToLine;
      Collinear A C F  ∧  F ∈ ray D B ━ {D}  ∧  C ∈ int_angle A D F     [] by fol Fexists IN_DIFF IN_SING IN_Ray B1' IntervalRayEZ CintADB InteriorWellDefined;
      C ∈ Open (A, F)     [] by fol - AlternateConverseCrossbar;
      ∡ A D C suppl ∡ C D E  ∧  ∡ A C D suppl ∡ D C F     [] by fol ADE DACncol - SupplementaryAngles_DEF;
      ∡ C D E ≡ ∡ D C F     [CDEeqDCF] by fol - CDAeqDCA AngleSymmetry SupplementsCongAnglesCong;
      ∡ C D B <_ang ∡ C D E     [] by fol angCDB CDEncol BintCDE C5Reflexive AngleOrdering_DEF;
      ∡ C D B <_ang ∡ D C F     [CDBlessDCF] by fol - DCFncol ANGLE CDEeqDCF AngleTrichotomy2;
      ∡ D C F <_ang ∡ D C B     [] by fol DCFncol ANGLE angCDB FintBCD InteriorAngleSymmetry C5Reflexive AngleOrdering_DEF;
      ∡ C D B <_ang ∡ D C B     [] by fol CDBlessDCF - AngleOrderTransitivity;
      ¬(∡ D C B ≡ ∡ C D B)     [] by fol - AngleTrichotomy1 angCDB CollinearSymmetry ANGLE C5Symmetric;
      fol Distinct ADCncol CollinearSymmetry - IsoscelesCongBaseAngles;
    end;
  qed;
`;;

let EuclidPropositionI_7 = theorem `;
  ∀A B C D a.  ¬(A = B)  ⇒  Line a ∧ A ∈ a ∧ B ∈ a  ⇒
    ¬(C = D) ∧ C ∉ a ∧ D ∉ a ∧ C,D same_side a  ⇒
    seg A C ≡ seg A D
   ⇒  ¬(seg B C ≡ seg B D)

  proof
    intro_TAC ∀A B C D a, notAB, a_line, Csim_aD, ACeqAD;
    ¬Collinear A B C ∧ ¬Collinear D A B     [ABCncol] by fol a_line notAB Csim_aD NonCollinearRaa CollinearSymmetry;
    ¬(A = C) ∧ ¬(A = D) ∧ ¬(B = C) ∧ ¬(B = D) ∧ A ∉ Open (C, D)     [Distinct] by fol a_line Csim_aD ∉ SameSide_DEF;
    ¬Collinear A D C      [ADCncol]
    proof
      assume Collinear A D C     [Con] by fol -;
      C ∈ ray A D ━ {A}  ∧  D ∈ ray A D ━ {A}  ∧  seg A D ≡ seg A D     [] by fol Distinct - IN_Ray EndpointInRay IN_DIFF IN_SING SEGMENT C2Reflexive;
      fol Distinct SEGMENT - ACeqAD C1 Csim_aD;
    qed;
    D,C same_side a     [Dsim_aC] by fol a_line Csim_aD SameSideSymmetric;
    seg A D ≡ seg A C  ∧  seg B D ≡ seg B D     [ADeqAC] by fol Distinct SEGMENT ACeqAD C2Symmetric C2Reflexive;
    ¬Collinear D A C ∧ ¬Collinear C D A ∧ ¬Collinear A C D ∧ ¬Collinear A D C     [DACncol] by fol ADCncol CollinearSymmetry;
    ¬(seg B D ≡ seg B C)  ⇒  ¬(seg B C ≡ seg B D)     [BswitchDC] by fol Distinct SEGMENT C2Symmetric;
    case_split BDCcol | BDCncol     by fol -;
    suppose Collinear B D C;
      B ∉ Open (C, D)  ∧  C ∈ ray B D ━ {B}  ∧  D ∈ ray B D ━ {B}     [] by fol a_line Csim_aD SameSide_DEF ∉ Distinct - IN_Ray Distinct IN_DIFF IN_SING EndpointInRay;
      fol Distinct SEGMENT - ACeqAD ADeqAC C1 Csim_aD;
    end;
    suppose ¬Collinear B D C;
      Tetralateral A B C D     [] by fol notAB Distinct Csim_aD ABCncol - CollinearSymmetry DACncol Tetralateral_DEF;
      ConvexQuadrilateral A B C D  ∨  C ∈ int_triangle D A B  ∨
      ConvexQuadrilateral A B D C  ∨  D ∈ int_triangle C A B     [] by fol - a_line Csim_aD  FourChoicesTetralateral InteriorTriangleSymmetry;
      fol notAB a_line Csim_aD Dsim_aC ACeqAD ADeqAC - EuclidPropositionI_7Help BswitchDC;
    end;
  qed;
`;;

let EuclidPropositionI_11 = theorem `;
  ∀A B. ¬(A = B)  ⇒  ∃F. Right (∡ A B F)

  proof
    intro_TAC ∀A B, notAB;
    consider C such that
    B ∈ Open (A, C)  ∧  seg B C ≡ seg B A     [ABC] by fol notAB SEGMENT C1OppositeRay;
    ¬(A = B) ∧ ¬(A = C) ∧ ¬(B = C) ∧ Collinear A B C     [Distinct] by fol ABC B1';
    seg B A ≡ seg B C     [BAeqBC] by fol - SEGMENT ABC C2Symmetric;
    consider F such that
    ¬Collinear A F C  ∧  seg F A  ≡ seg F C     [Fexists] by fol Distinct IsoscelesExists;
    ¬Collinear B F A ∧ ¬Collinear B F C     [BFAncol] by fol - CollinearSymmetry Distinct NoncollinearityExtendsToLine;
    ¬Collinear A B F ∧ Angle (∡ A B F)     [angABF] by fol BFAncol CollinearSymmetry ANGLE;
    ∡ A B F suppl ∡ F B C     [ABFsuppl] by fol - ABC SupplementaryAngles_DEF;
    ¬(B = F)  ∧  seg B F ≡ seg B F     [] by fol BFAncol NonCollinearImpliesDistinct SEGMENT C2Reflexive;
    B,F,A ≅ B,F,C     [] by fol BFAncol - BAeqBC Fexists SSS;
    ∡ A B F ≡ ∡ F B C     [] by fol - TriangleCong_DEF AngleSymmetry;
    fol angABF ABFsuppl - RightAngle_DEF;
  qed;
`;;

let DropPerpendicularToLine = theorem `;
  ∀P l.  Line l  ∧  P ∉ l  ⇒  ∃E Q. E ∈ l ∧ Q ∈ l ∧ Right (∡ P Q E)

  proof
    intro_TAC ∀P l, l_line;
    consider A B such that
    A ∈ l ∧ B ∈ l ∧ ¬(A = B)     [ABl] by fol l_line I2;
    ¬Collinear B A P ∧ ¬Collinear P A B ∧ ¬(A = P)     [BAPncol] by fol ABl l_line NonCollinearRaa CollinearSymmetry ∉;
    Angle (∡ B A P) ∧ Angle (∡ P A B)     [angBAP] by fol - ANGLE AngleSymmetry;
    consider P' such that
    ¬(A = P') ∧ P' ∉ l ∧ ¬(P,P' same_side l) ∧ seg A P' ≡ seg A P  ∧  ∡ B A P' ≡ ∡ B A P     [P'exists] by simplify C4OppositeSide - ABl BAPncol l_line;
    consider Q such that
    Q ∈ l ∧ Q ∈ Open (P, P') ∧ Collinear A B Q     [Qexists] by fol l_line - SameSide_DEF ABl Collinear_DEF;
    ¬Collinear B A P'     [BAP'ncol] by fol l_line ABl I1 Collinear_DEF P'exists ∉;
    ∡ B A P ≡ ∡ B A P'     [BAPeqBAP'] by fol - ANGLE angBAP P'exists C5Symmetric;
    ∃E. E ∈ l  ∧  ¬Collinear P Q E  ∧  ∡ P Q E ≡ ∡ E Q P'     []
    proof
      assume ¬(A = Q) [notAQ] by fol ABl - BAPncol BAPeqBAP' AngleSymmetry;
      seg A Q  ≡ seg A Q  ∧  seg A P ≡ seg A P'     [APeqAP'] by fol - SEGMENT C2Reflexive BAPncol P'exists C2Symmetric;
      ¬Collinear Q A P' ∧ ¬Collinear Q A P     [QAP'ncol] by fol notAQ l_line ABl Qexists P'exists NonCollinearRaa CollinearSymmetry;
      ∡ Q A P ≡ ∡ Q A P'     []
      proof
        case_split QAB | notQAB     by fol - ∉;
        suppose A ∈ Open (Q, B);
          ∡ B A P suppl ∡ P A Q   ∧  ∡ B A P' suppl ∡ P' A Q     [] by fol BAPncol BAP'ncol - B1'  SupplementaryAngles_DEF;
          fol - BAPeqBAP' SupplementsCongAnglesCong AngleSymmetry;
        end;
        suppose A ∉ Open (Q, B);
          Q ∈ ray A B ━ {A}     [QrayAB_A] by fol ABl Qexists notQAB IN_Ray notAQ IN_DIFF IN_SING;
          ray A Q = ray A B     [] by fol - ABl RayWellDefined;
          fol notAQ QrayAB_A - BAPeqBAP' Angle_DEF;
        end;
      qed;
      Q,A,P ≅ Q,A,P'     [] by fol QAP'ncol APeqAP' - SAS;
      fol - TriangleCong_DEF AngleSymmetry ABl QAP'ncol CollinearSymmetry;
    qed;
    consider E such that
    E ∈ l ∧ ¬Collinear P Q E ∧ ∡ P Q E ≡ ∡ E Q P'     [Eexists] by fol -;
    ∡ P Q E suppl ∡ E Q P'  ∧  Right (∡ P Q E)     [] by fol - Qexists SupplementaryAngles_DEF RightAngle_DEF;
    fol Eexists Qexists -;
  qed;
`;;

let EuclidPropositionI_14 = theorem `;
  ∀A B C D l.  Line l ∧ A ∈ l ∧ B ∈ l ∧ ¬(A = B)  ⇒
    C ∉ l ∧ D ∉ l ∧ ¬(C,D same_side l)  ⇒ ∡ C B A suppl ∡ A B D
    ⇒  B ∈ Open (C, D)

  proof
    intro_TAC ∀A B C D l, l_line, Cnsim_lD, CBAsupplABD;
    ¬(B = C) ∧ ¬(B = D) ∧ ¬Collinear C B A     [Distinct] by fol l_line Cnsim_lD ∉ I1 Collinear_DEF;
    consider E such that
    B ∈ Open (C, E)     [CBE] by fol Distinct B2';
    E ∉ l ∧ ¬(C,E same_side l)     [Csim_lE] by fol l_line ∉ - BetweenLinear Cnsim_lD SameSide_DEF;
    D,E same_side l     [Dsim_lE] by fol l_line Cnsim_lD - AtMost2Sides;
    ∡ C B A suppl ∡ A B E     [] by fol Distinct CBE SupplementaryAngles_DEF;
    ∡ A B D ≡ ∡ A B E     [] by fol CBAsupplABD - SupplementUnique;
    ray B E = ray B D     [] by fol l_line Csim_lE Cnsim_lD Dsim_lE - C4Uniqueness;
    D ∈ ray B E ━ {B}     [] by fol Distinct - EndpointInRay IN_DIFF IN_SING;
    fol CBE - OppositeRaysIntersect1pointHelp B1';
  qed;
`;;

(* Euclid's Proposition I.15 *)

let VerticalAnglesCong = theorem `;
  ∀A B O A' B'.  ¬Collinear A O B  ⇒ O ∈ Open (A, A')  ∧  O ∈ Open (B, B')
    ⇒  ∡ B O A' ≡ ∡ B' O A

  proof
    intro_TAC ∀A B O A' B', H1, H2;
    ∡ A O B suppl ∡ B O A'     [AOBsupplBOA'] by fol H1 H2 SupplementaryAngles_DEF;
    ∡ B O A suppl ∡ A O B'     [] by fol H1 CollinearSymmetry H2 SupplementaryAngles_DEF;
    fol AOBsupplBOA' - AngleSymmetry SupplementUnique;
  qed;
`;;

let EuclidPropositionI_16 = theorem `;
  ∀A B C D. ¬Collinear A B C  ∧  C ∈ Open (B, D)
    ⇒  ∡ B A C <_ang ∡ D C A

  proof
    intro_TAC ∀A B C D, H1 H2;
    ¬(A = B) ∧ ¬(A = C) ∧ ¬(B = C)     [Distinct] by fol H1 NonCollinearImpliesDistinct;
    consider l such that
    Line l ∧ A ∈ l ∧ C ∈ l     [l_line] by fol Distinct I1;
    consider m such that
    Line m ∧ B ∈ m ∧ C ∈ m     [m_line] by fol Distinct I1;
    D ∈ m     [Dm] by fol m_line H2 BetweenLinear;
    consider E such that
    E ∈ Open (A, C) ∧ seg A E ≡ seg E C     [AEC] by fol Distinct MidpointExists;
    ¬(A = E) ∧ ¬(E = C) ∧ Collinear A E C ∧ ¬(B = E)     [AECcol] by fol - B1' H1;
    E ∈ l     [El] by fol l_line AEC BetweenLinear;
    consider F such that
    E ∈ Open (B, F) ∧ seg E F ≡ seg E B     [BEF] by fol AECcol SEGMENT C1OppositeRay;
    ¬(B = E) ∧ ¬(B = F) ∧ ¬(E = F) ∧ Collinear B E F     [BEF'] by fol BEF B1';
    B ∉ l     [notBl] by fol l_line Distinct I1 Collinear_DEF H1 ∉;
    ¬Collinear A E B ∧ ¬Collinear C E B     [AEBncol] by fol AECcol l_line El notBl NonCollinearRaa CollinearSymmetry;
    Angle (∡ B A E)     [angBAE] by fol - CollinearSymmetry ANGLE;
    ¬Collinear C E F     [CEFncol] by fol AEBncol BEF' CollinearSymmetry NoncollinearityExtendsToLine;
    ∡ B E A ≡ ∡ F E C     [BEAeqFEC] by fol AEBncol AEC B1' BEF VerticalAnglesCong;
    seg E A ≡ seg E C  ∧  seg E B ≡ seg E F     [] by fol AEC SegmentSymmetry AECcol BEF'  SEGMENT BEF C2Symmetric;
    A,E,B ≅ C,E,F     [] by fol AEBncol CEFncol - BEAeqFEC AngleSymmetry SAS;
    ∡ B A E ≡ ∡ F C E     [BAEeqFCE] by fol - TriangleCong_DEF;
    ¬Collinear E C D     [ECDncol] by fol AEBncol H2 B1' CollinearSymmetry NoncollinearityExtendsToLine;
    F ∉ l ∧ D ∉ l     [notFl] by fol l_line El Collinear_DEF CEFncol - ∉;
    F ∈ ray B E ━ {B}  ∧  E ∉ m     [] by fol BEF IntervalRayEZ m_line Collinear_DEF AEBncol ∉;
    F ∉ m  ∧  F,E same_side m     [Fsim_mE] by fol m_line - RaySameSide;
    ¬(B,F same_side l)  ∧  ¬(B,D same_side l)     [] by fol El l_line BEF H2 SameSide_DEF;
    F,D same_side l     [] by fol l_line notBl notFl - AtMost2Sides;
    F ∈ int_angle E C D     [] by fol ECDncol l_line El m_line Dm notFl Fsim_mE - IN_InteriorAngle;
    ∡ B A E <_ang ∡ E C D     [BAElessECD] by fol angBAE ECDncol - BAEeqFCE AngleSymmetry AngleOrdering_DEF;
    ray A E = ray A C  ∧  ray C E = ray C A     [] by fol AEC B1' IntervalRay;
    ∡ B A C <_ang ∡ A C D     [] by fol BAElessECD - Angle_DEF;
    fol - AngleSymmetry;
  qed;
`;;

let ExteriorAngle = theorem `;
  ∀A B C D.  ¬Collinear A B C  ∧  C ∈ Open (B, D)
    ⇒  ∡ A B C <_ang ∡ A C D

  proof
    intro_TAC ∀A B C D, H1 H2;
    ¬(C = D) ∧ C ∈ Open (D, B) ∧ Collinear B C D     [H2'] by fol H2 BetweenLinear B1';
    ¬Collinear B A C ∧ ¬(A = C)     [BACncol] by fol H1 CollinearSymmetry NonCollinearImpliesDistinct;
    consider E such that
    C ∈ Open (A, E)     [ACE] by fol - B2';
    ¬(C = E) ∧ C ∈ Open (E, A) ∧ Collinear A C E     [ACE'] by fol - B1';
    ¬Collinear A C D ∧ ¬Collinear D C E     [DCEncol] by fol H1 CollinearSymmetry H2' - NoncollinearityExtendsToLine;
    ∡ A B C <_ang ∡ E C B     [ABClessECB] by fol BACncol ACE EuclidPropositionI_16;
    ∡ E C B ≡ ∡ A C D     [] by fol DCEncol ACE' H2' VerticalAnglesCong;
    fol ABClessECB DCEncol ANGLE - AngleTrichotomy2;
  qed;
`;;

let EuclidPropositionI_17 = theorem `;
  ∀A B C α β γ.  ¬Collinear A B C  ∧  α = ∡ A B C  ∧  β = ∡ B C A  ⇒
    β suppl γ
    ⇒  α <_ang γ

  proof
    intro_TAC ∀A B C α β γ, H1, H2;
    Angle γ     [angγ] by fol H2 SupplementImpliesAngle;
    ¬(A = B) ∧ ¬(A = C) ∧ ¬(B = C)     [Distinct] by fol H1 NonCollinearImpliesDistinct;
    ¬Collinear B A C ∧ ¬Collinear A C B     [BACncol] by fol H1 CollinearSymmetry;
    consider D such that
    C ∈ Open (A, D)     [ACD] by fol Distinct B2';
    ∡ A B C <_ang ∡ D C B     [ABClessDCB] by fol BACncol ACD EuclidPropositionI_16;
    β suppl ∡ B C D     [] by fol - H1 AngleSymmetry BACncol ACD SupplementaryAngles_DEF;
    ∡ B C D ≡ γ     [] by fol H2 - SupplementUnique;
    fol ABClessDCB H1 AngleSymmetry angγ - AngleTrichotomy2;
  qed;
`;;

let EuclidPropositionI_18 = theorem `;
  ∀A B C.  ¬Collinear A B C  ∧  seg A C <__ seg A B
    ⇒  ∡ A B C <_ang ∡ B C A

  proof
    intro_TAC ∀A B C, H1 H2;
    ¬(A = B) ∧ ¬(A = C)     [Distinct] by fol H1 NonCollinearImpliesDistinct;
    consider D such that
    D ∈ Open (A, B) ∧ seg A C ≡ seg A D     [ADB] by fol Distinct SEGMENT H2 SegmentOrderingUse;
    ¬(D = A) ∧ ¬(D = B) ∧ D ∈ Open (B, A) ∧ Collinear A D B ∧ ray B D = ray B A     [ADB'] by fol - B1' IntervalRay;
    D ∈ int_angle A C B  ∧ ¬Collinear A C B      [DintACB] by fol H1 CollinearSymmetry ADB ConverseCrossbar;
    ¬Collinear D A C ∧ ¬Collinear C B D ∧ ¬Collinear C D A     [DACncol] by fol H1 CollinearSymmetry ADB' NoncollinearityExtendsToLine;
    seg A D ≡ seg A C     [] by fol ADB' Distinct SEGMENT ADB C2Symmetric;
    ∡ C D A ≡ ∡ A C D     [] by fol DACncol - IsoscelesCongBaseAngles AngleSymmetry;
    ∡ C D A <_ang ∡ A C B     [CDAlessACB] by fol DACncol ANGLE H1 DintACB - AngleOrdering_DEF;
    ∡ B D C suppl ∡ C D A     [] by fol DACncol CollinearSymmetry ADB' SupplementaryAngles_DEF;
    ∡ C B D <_ang ∡ C D A     [] by fol DACncol - EuclidPropositionI_17;
    ∡ C B D <_ang ∡ A C B     [] by fol - CDAlessACB AngleOrderTransitivity;
    fol - ADB' Angle_DEF AngleSymmetry;
  qed;
`;;

let EuclidPropositionI_19 = theorem `;
  ∀A B C. ¬Collinear A B C  ∧  ∡ A B C <_ang ∡ B C A
    ⇒  seg A C  <__ seg A B

  proof
    intro_TAC ∀A B C, H1 H2;
    ¬Collinear B A C ∧ ¬Collinear B C A ∧ ¬Collinear A C B     [BACncol] by fol H1 CollinearSymmetry;
    ¬(A = B) ∧ ¬(A = C)     [Distinct] by fol H1 NonCollinearImpliesDistinct;
    assume ¬(seg A C  <__ seg A B)     [Con] by fol -;
    seg A B ≡ seg A C   ∨  seg A B  <__ seg A C     [] by fol Distinct SEGMENT - SegmentTrichotomy;
    case_split cong | less     by fol -;
    suppose seg A B ≡ seg A C;
      ∡ C B A ≡ ∡ B C A     [] by fol BACncol - IsoscelesCongBaseAngles;
      fol - AngleSymmetry H2 AngleTrichotomy1;
    end;
    suppose seg A B  <__ seg A C;
      ∡ A C B <_ang ∡ C B A     [] by fol BACncol - EuclidPropositionI_18;
      fol H1 BACncol ANGLE - AngleSymmetry H2 AngleTrichotomy;
    end;
  qed;
`;;

let EuclidPropositionI_20 = theorem `;
  ∀A B C D. ¬Collinear A B C  ⇒  A ∈ Open (B, D)  ∧  seg A D ≡ seg A C
    ⇒  seg B C <__ seg B D

  proof
    intro_TAC ∀A B C D, H1, H2;
    ¬(B = D) ∧ ¬(A = D) ∧ A ∈ Open (D, B) ∧ Collinear B A D ∧ ray D A = ray D B     [BAD'] by fol H2 B1' IntervalRay;
    ¬Collinear C A D     [CADncol] by fol H1 CollinearSymmetry BAD' NoncollinearityExtendsToLine;
    ¬Collinear D C B ∧ ¬Collinear B D C     [DCBncol] by fol H1 CollinearSymmetry BAD' NoncollinearityExtendsToLine;
    Angle (∡ C D A)     [angCDA] by fol CADncol CollinearSymmetry ANGLE;
    ∡ C D A ≡ ∡ D C A     [CDAeqDCA] by fol CADncol CollinearSymmetry H2 IsoscelesCongBaseAngles;
    A ∈ int_angle D C B     [] by fol DCBncol BAD' ConverseCrossbar;
    ∡ C D A <_ang ∡ D C B     [] by fol angCDA DCBncol - CDAeqDCA AngleOrdering_DEF;
    ∡ B D C <_ang ∡ D C B     [] by fol - BAD' Angle_DEF AngleSymmetry;
    fol DCBncol - EuclidPropositionI_19;
  qed;
`;;

let EuclidPropositionI_21 = theorem `;
  ∀A B C D. ¬Collinear A B C  ∧  D ∈ int_triangle A B C
    ⇒  ∡ A B C <_ang ∡ C D A

  proof
    intro_TAC ∀A B C D, H1 H2;
    ¬(B = A) ∧ ¬(B = C) ∧ ¬(A = C)     [Distinct] by fol H1 NonCollinearImpliesDistinct;
    D ∈ int_angle B A C  ∧  D ∈ int_angle C B A     [DintTri] by fol H2 IN_InteriorTriangle InteriorAngleSymmetry;
    consider E such that
    E ∈ Open (B, C) ∧ E ∈ ray A D ━ {A}     [BEC] by fol - Crossbar_THM;
    ¬(B = E) ∧ ¬(E = C) ∧ Collinear B E C  ∧  Collinear A D E      [BEC'] by fol - B1' IN_Ray IN_DIFF IN_SING;
    ray B E = ray B C  ∧  E ∈ ray B C ━ {B}     [rBErBC] by fol BEC IntervalRay IntervalRayEZ;
    D ∈ int_angle A B E     [DintABE] by fol DintTri - InteriorAngleSymmetry InteriorWellDefined;
    D ∈ Open (A, E)     [ADE] by fol BEC' - AlternateConverseCrossbar;
    ray E D = ray E A     [rEDrEA] by fol - B1' IntervalRay;
    ¬Collinear A B E ∧ ¬Collinear B E A  ∧ ¬Collinear C B D ∧ ¬(A = D)     [ABEncol] by fol DintABE IN_InteriorAngle CollinearSymmetry DintTri InteriorEZHelp;
    ¬Collinear E D C ∧ ¬Collinear C E D     [EDCncol] by fol - CollinearSymmetry BEC'  NoncollinearityExtendsToLine;
    ∡ A B E <_ang ∡ A E C  ∧  ∡ C E D = ∡ D E C     [] by fol ABEncol BEC ExteriorAngle AngleSymmetry;
    ∡ A B C <_ang ∡ C E D     [ABClessAEC] by fol - rBErBC rEDrEA Angle_DEF;
    ∡ C E D  <_ang  ∡ C D A     [] by fol EDCncol ADE B1' ExteriorAngle;
    fol ABClessAEC - AngleOrderTransitivity;
  qed;
`;;

let AngleTrichotomy3 = theorem `;
  ∀α β γ.  α <_ang β  ∧  Angle γ  ∧  γ ≡ α  ⇒  γ <_ang β

  proof
    intro_TAC ∀α β γ, H1;
    consider A O B G such that
    Angle α ∧ ¬Collinear A O B ∧ β = ∡ A O B ∧ G ∈ int_angle A O B ∧ α ≡ ∡ A O G     [H1'] by fol H1 AngleOrdering_DEF;
    ¬Collinear A O G     [] by fol - InteriorEZHelp;
    γ ≡ ∡ A O G     [] by fol H1 H1' - ANGLE C5Transitive;
    fol H1 H1' - AngleOrdering_DEF;
  qed;
`;;

let InteriorCircleConvexHelp = theorem `;
  ∀O A B C. ¬Collinear A O C  ⇒  B ∈ Open (A, C)  ⇒
    seg O A <__ seg O C  ∨  seg O A ≡ seg O C
    ⇒  seg O B <__ seg O C

  proof
    intro_TAC ∀O A B C, H1, H2, H3;
    ¬Collinear O C A ∧ ¬Collinear C O A ∧ ¬(O = A) ∧ ¬(O = C)     [H1'] by fol H1 CollinearSymmetry NonCollinearImpliesDistinct;
    ray A B = ray A C  ∧  ray C B = ray C A     [equal_rays] by fol H2 IntervalRay B1';
    ∡ O C A <_ang ∡ C A O  ∨  ∡ O C A ≡ ∡ C A O     []
    proof
      assume seg O A ≡ seg O C [seg_eq] by fol H3 H1' - EuclidPropositionI_18;
      seg O C ≡ seg O A     [] by fol H1' SEGMENT - C2Symmetric;
      fol H1' - IsoscelesCongBaseAngles AngleSymmetry;
    qed;
    ∡ O C B <_ang ∡ B A O  ∨  ∡ O C B ≡ ∡ B A O     [] by fol - equal_rays Angle_DEF;
    ∡ B C O <_ang ∡ O A B  ∨  ∡ B C O ≡ ∡ O A B     [BCOlessOAB] by fol - AngleSymmetry;
    ¬Collinear O A B ∧ ¬Collinear B C O ∧ ¬Collinear O C B     [OABncol] by fol H1 CollinearSymmetry H2 B1' NoncollinearityExtendsToLine;
    ∡ O A B <_ang ∡ O B C     [] by fol - H2 ExteriorAngle;
    ∡ B C O <_ang ∡ O B C     [] by fol BCOlessOAB - AngleOrderTransitivity OABncol ANGLE - AngleTrichotomy3;
    fol OABncol - AngleSymmetry EuclidPropositionI_19;
  qed;
`;;

let InteriorCircleConvex = theorem `;
  ∀O R A B C.  ¬(O = R)  ⇒  B ∈ Open (A, C)  ⇒
    A ∈ int_circle O R  ∧  C ∈ int_circle O R
    ⇒  B ∈ int_circle O R

  proof
    intro_TAC ∀O R A B C, H1, H2, H3;
    ¬(A = B) ∧ ¬(A = C) ∧ ¬(B = C) ∧ B ∈ Open (C, A)     [H2'] by fol H2 B1';
    (A = O  ∨  seg O A <__ seg O R)  ∧  (C = O  ∨  seg O C <__ seg O R)     [ACintOR] by fol H3 H1 IN_InteriorCircle;
    case_split OAC | OnotAC     by fol -;
    suppose O = A ∨ O = C;
      B ∈ Open (O, C)  ∨  B ∈ Open (O, A)     [] by fol - H2 B1';
      seg O B <__ seg O A ∧ ¬(O = A)  ∨  seg O B <__ seg O C ∧ ¬(O = C)     [] by fol - B1' SEGMENT C2Reflexive  SegmentOrdering_DEF;
      seg O B <__ seg O R     [] by fol - ACintOR SegmentOrderTransitivity;
      fol - H1 IN_InteriorCircle;
    end;
    suppose ¬(O = A) ∧ ¬(O = C);
      case_split AOCncol | AOCcol     by fol -;
      suppose ¬Collinear A O C;
        seg O A <__ seg O C  ∨  seg O A ≡ seg O C  ∨  seg O C <__ seg O A     [] by fol OnotAC SEGMENT  SegmentTrichotomy;
        seg O B <__ seg O C  ∨  seg O B <__ seg O A     [] by fol AOCncol H2 - InteriorCircleConvexHelp CollinearSymmetry B1';
        fol OnotAC ACintOR - SegmentOrderTransitivity H1 IN_InteriorCircle;
      end;
      suppose Collinear A O C;
        consider l such that
        Line l ∧ A ∈ l ∧ C ∈ l     [l_line] by fol H2' I1;
        Collinear B A O ∧ Collinear B C O     [OABCcol] by fol - H2 BetweenLinear H2' AOCcol CollinearLinear Collinear_DEF;
        B ∉ Open (O, A) ∧ B ∉ Open (O, C)  ⇒  B = O     []
        proof
          intro_TAC Assumption;
          O ∈ ray B A ∩ ray B C     [] by fol H2' OABCcol - IN_Ray IN_INTER;
          fol - H2 OppositeRaysIntersect1point IN_SING;
        qed;
        B ∈ Open (O, A)  ∨  B ∈ Open (O, C)  ∨  B = O     [] by fol - ∉;
        seg O B <__ seg O A  ∨  seg O B <__ seg O C  ∨  B = O     [] by fol - B1' SEGMENT C2Reflexive  SegmentOrdering_DEF;
        seg O B <__ seg O R  ∨  B = O     [] by fol - ACintOR OnotAC SegmentOrderTransitivity;
        fol - H1 IN_InteriorCircle;
      end;
    end;
  qed;
`;;

let SegmentTrichotomy3 = theorem `;
  ∀s t u.  s <__ t  ∧  Segment u  ∧  u ≡ s  ⇒  u <__ t

  proof
    intro_TAC ∀s t u, H1;
    consider C D X such that
    Segment s ∧ t = seg C D ∧ X ∈ Open (C, D) ∧ s ≡ seg C X ∧ ¬(C = X)     [H1'] by fol H1 SegmentOrdering_DEF B1';
    u ≡ seg C X     [] by fol H1 - SEGMENT C2Transitive;
    fol H1 H1' - SegmentOrdering_DEF;
  qed;
`;;

let EuclidPropositionI_24Help = theorem `;
  ∀O A C O' D M.  ¬Collinear A O C ∧ ¬Collinear D O' M  ⇒
    seg O' D ≡ seg O A  ∧  seg O' M ≡ seg O C  ⇒  ∡ D O' M <_ang ∡ A O C  ⇒
    seg O A <__ seg O C  ∨  seg O A ≡ seg O C
    ⇒  seg D M <__ seg A C

  proof
    intro_TAC ∀O A C O' D M, H1, H2, H3, H4;
    consider K such that
    K ∈ int_angle A O C ∧ ∡ D O' M ≡ ∡ A O K     [KintAOC] by fol H1 ANGLE H3 AngleOrderingUse;
    ¬(O = C) ∧ ¬(D = M) ∧ ¬(O' = M) ∧ ¬(O = K)     [Distinct] by fol H1 NonCollinearImpliesDistinct - InteriorEZHelp;
    consider B such that
    B ∈ ray O K ━ {O}  ∧  seg O B ≡ seg O C     [BrOK] by fol Distinct SEGMENT - C1;
    ray O B = ray O K     [] by fol Distinct - RayWellDefined;
    ∡ D O' M ≡ ∡ A O B     [DO'MeqAOB] by fol KintAOC - Angle_DEF;
    B ∈ int_angle A O C     [BintAOC] by fol KintAOC BrOK WholeRayInterior;
    ¬(B = O) ∧ ¬Collinear A O B     [AOBncol] by fol - InteriorEZHelp;
    seg O C ≡ seg O B     [OCeqOB] by fol Distinct - SEGMENT BrOK C2Symmetric;
    seg O' M ≡ seg O B     [] by fol Distinct SEGMENT AOBncol H2 - C2Transitive;
    D,O',M ≅ A,O,B     [] by fol H1 AOBncol H2 - DO'MeqAOB SAS;
    seg D M ≡ seg A B     [DMeqAB] by fol - TriangleCong_DEF;
    consider G such that
    G ∈ Open (A, C)  ∧  G ∈ ray O B ━ {O}  ∧  ¬(G = O)     [AGC] by fol BintAOC Crossbar_THM B1' IN_DIFF IN_SING;
    Segment (seg O G) ∧ ¬(O = B)     [notOB] by fol - SEGMENT BrOK IN_DIFF IN_SING;
    seg O G <__ seg O C     [] by fol H1 AGC H4 InteriorCircleConvexHelp;
    seg O G <__ seg O B     [] by fol - OCeqOB BrOK SEGMENT SegmentTrichotomy2 IN_DIFF IN_SING;
    consider G' such that
    G' ∈ Open (O, B)  ∧  seg O G ≡ seg O G'     [OG'B] by fol notOB - SegmentOrderingUse;
    ¬(G' = O)  ∧  seg O G' ≡ seg O G'  ∧  Segment (seg O G')     [notG'O] by fol - B1' SEGMENT C2Reflexive SEGMENT;
    G' ∈ ray O B ━ {O}     [] by fol OG'B IntervalRayEZ;
    G' = G  ∧  G ∈ Open (B, O)     [] by fol notG'O notOB - AGC OG'B C1 B1';
    ConvexQuadrilateral B A O C     [] by fol H1 - AGC DiagonalsIntersectImpliesConvexQuad;
    A ∈ int_angle O C B  ∧  O ∈ int_angle C B A  ∧  Quadrilateral B A O C     [OintCBA] by fol - ConvexQuad_DEF;
    A ∈ int_angle B C O     [AintBCO] by fol - InteriorAngleSymmetry;
    Tetralateral B A O C     [] by fol OintCBA Quadrilateral_DEF;
    ¬Collinear C B A  ∧ ¬Collinear B C O ∧ ¬Collinear C O B ∧ ¬Collinear C B O     [BCOncol] by fol - Tetralateral_DEF CollinearSymmetry;
    ∡ B C O ≡ ∡ C B O     [BCOeqCBO] by fol - OCeqOB IsoscelesCongBaseAngles;
    ¬Collinear B C A ∧ ¬Collinear A C B     [ACBncol] by fol AintBCO InteriorEZHelp CollinearSymmetry;
    ∡ B C A ≡ ∡ B C A  ∧  Angle (∡ B C A)  ∧  ∡ C B O ≡ ∡ C B O     [CBOref] by fol - ANGLE BCOncol C5Reflexive;
    ∡ B C A <_ang ∡ B C O     [] by fol - BCOncol ANGLE AintBCO AngleOrdering_DEF;
    ∡ B C A <_ang ∡ C B O     [BCAlessCBO] by fol - BCOncol ANGLE BCOeqCBO AngleTrichotomy2;
    ∡ C B O <_ang ∡ C B A     [] by fol BCOncol ANGLE OintCBA CBOref AngleOrdering_DEF;
    ∡ A C B <_ang ∡ C B A     [] by fol BCAlessCBO - AngleOrderTransitivity AngleSymmetry;
    seg A B <__ seg A C     [] by fol ACBncol - EuclidPropositionI_19;
    fol - Distinct SEGMENT DMeqAB SegmentTrichotomy3;
 qed;
`;;

let EuclidPropositionI_24 = theorem `;
  ∀O A C O' D M. ¬Collinear A O C ∧ ¬Collinear D O' M  ⇒
    seg O' D ≡ seg O A ∧ seg O' M ≡ seg O C  ⇒  ∡ D O' M <_ang ∡ A O C
    ⇒  seg D M <__ seg A C

  proof
    intro_TAC ∀O A C O' D M, H1, H2, H3;
    ¬(O = A) ∧ ¬(O = C) ∧ ¬Collinear C O A ∧ ¬Collinear M O' D     [Distinct] by fol H1 NonCollinearImpliesDistinct CollinearSymmetry;
    seg O A ≡ seg O C  ∨  seg O A <__ seg O C  ∨  seg O C <__ seg O A     [3pos] by fol  - SEGMENT SegmentTrichotomy;
    assume seg O C <__ seg O A [H4] by fol 3pos H1 H2 H3 - EuclidPropositionI_24Help;
    ∡ M O' D <_ang ∡ C O A     [] by fol H3 AngleSymmetry;
    fol Distinct H3 AngleSymmetry H2 H4 EuclidPropositionI_24Help SegmentSymmetry;
  qed;
`;;

let EuclidPropositionI_25 = theorem `;
  ∀O A C O' D M.  ¬Collinear A O C ∧ ¬Collinear D O' M  ⇒
    seg O' D ≡ seg O A ∧ seg O' M ≡ seg O C  ⇒  seg D M <__ seg A C
    ⇒  ∡ D O' M <_ang ∡ A O C

  proof
    intro_TAC ∀O A C O' D M, H1, H2, H3;
    ¬(O = A) ∧ ¬(O = C) ∧ ¬(A = C) ∧ ¬(D = M) ∧ ¬(O' = D) ∧ ¬(O' = M)     [Distinct] by fol H1 NonCollinearImpliesDistinct;
    assume ¬(∡ D O' M <_ang ∡ A O C)     [Contradiction] by fol -;
    ∡ D O' M ≡ ∡ A O C  ∨  ∡ A O C <_ang ∡ D O' M     [] by fol H1 ANGLE - AngleTrichotomy;
    case_split Cong | Con     by fol -;
    suppose ∡ D O' M ≡ ∡ A O C;
      D,O',M ≅ A,O,C     [] by fol H1 H2 - SAS;
      seg D M ≡ seg A C     [] by fol - TriangleCong_DEF;
      fol Distinct SEGMENT - H3 SegmentTrichotomy;
    end;
    suppose ∡ A O C <_ang ∡ D O' M;
      seg O A ≡ seg O' D  ∧  seg O C  ≡ seg O' M     [H2'] by fol Distinct SEGMENT H2 C2Symmetric;
      seg A C <__ seg D M     [] by fol H1 - Con EuclidPropositionI_24;
      fol Distinct SEGMENT - H3 SegmentTrichotomy;
    end;
  qed;
`;;

let AAS = theorem `;
  ∀A B C A' B' C'. ¬Collinear A B C ∧ ¬Collinear A' B' C'  ⇒
    ∡ A B C ≡ ∡ A' B' C'  ∧  ∡ B C A ≡ ∡ B' C' A'  ⇒  seg A B ≡ seg A' B'
    ⇒  A,B,C ≅ A',B',C'

  proof
    intro_TAC ∀A B C A' B' C', H1, H2, H3;
    ¬(A = B) ∧ ¬(B = C) ∧ ¬(B' = C')     [Distinct] by fol H1 NonCollinearImpliesDistinct;
    consider G such that
    G ∈ ray B C ━ {B} ∧ seg B G ≡ seg B' C'     [Gexists] by fol Distinct SEGMENT C1;
    ¬(G = B)  ∧  B ∉ Open (G, C)  ∧ Collinear G B C     [notGBC] by fol - IN_Ray CollinearSymmetry IN_DIFF IN_SING;
    ¬Collinear A B G ∧ ¬Collinear B G A     [ABGncol] by fol H1 notGBC CollinearSymmetry NoncollinearityExtendsToLine;
    ray B G = ray B C     [] by fol Distinct Gexists RayWellDefined;
    ∡ A B G = ∡ A B C     [] by fol Distinct - Angle_DEF;
    A,B,G ≅ A',B',C'     [ABG≅A'B'C'] by fol H1 ABGncol H3 SegmentSymmetry H2 - Gexists SAS;
    ∡ B G A ≡ ∡ B' C' A'     [BGAeqB'C'A'] by fol - TriangleCong_DEF;
    ¬Collinear B C A  ∧ ¬Collinear B' C' A'     [BCAncol] by fol H1 CollinearSymmetry;
    ∡ B' C' A' ≡ ∡ B C A  ∧  ∡ B C A ≡ ∡ B C A     [BCArefl] by fol - ANGLE H2 C5Symmetric C5Reflexive;
    ∡ B G A ≡ ∡ B C A     [BGAeqBCA] by fol ABGncol BCAncol ANGLE BGAeqB'C'A' - C5Transitive;
    assume ¬(G = C) [notGC]     by fol BGAeqBCA - ABG≅A'B'C';
    ¬Collinear A C G ∧ ¬Collinear A G C     [ACGncol] by fol H1 notGBC - CollinearSymmetry NoncollinearityExtendsToLine;
    C ∈ Open (B, G) ∨ G ∈ Open (C, B)     [] by fol notGBC notGC Distinct B3' ∉;
    case_split BCG |  CGB by fol -;
    suppose C ∈ Open (B, G) ;
      C ∈ Open (G, B)  ∧ ray G C = ray G B     [rGCrBG] by fol - B1' IntervalRay;
      ∡ A G C <_ang ∡ A C B     [] by fol ACGncol - ExteriorAngle;
      ∡ B G A <_ang ∡ B C A     [] by fol - rGCrBG Angle_DEF AngleSymmetry AngleSymmetry;
      fol ABGncol BCAncol ANGLE - AngleSymmetry BGAeqBCA AngleTrichotomy;
    end;
    suppose G ∈ Open (C, B);
      ray C G = ray C B  ∧  ∡ A C G <_ang ∡ A G B     [] by fol - IntervalRay ACGncol ExteriorAngle;
      ∡ A C B <_ang ∡ B G A     [] by fol - Angle_DEF AngleSymmetry;
      ∡ B C A <_ang ∡ B C A     [] by fol - BCAncol ANGLE BGAeqBCA AngleTrichotomy2 AngleSymmetry;
      fol - BCArefl AngleTrichotomy1;
    end;
  qed;
`;;

let ParallelSymmetry = theorem `;
  ∀l k. l ∥ k  ⇒  k ∥ l
  by fol PARALLEL INTER_COMM`;;

let AlternateInteriorAngles = theorem `;
  ∀A B C E l m t.  Line l ∧ A ∈ l ∧ E ∈ l  ⇒
    Line m ∧ B ∈ m ∧ C ∈ m  ⇒  Line t ∧ A ∈ t ∧ B ∈ t  ⇒
    ¬(A = E) ∧ ¬(B = C) ∧ ¬(A = B) ∧ E ∉ t ∧ C ∉ t  ⇒
    ¬(C,E same_side t)  ⇒  ∡ E A B ≡ ∡ C B A
    ⇒  l ∥ m

  proof
    intro_TAC ∀A B C E l m t, l_line, m_line, t_line, Distinct, Cnsim_tE, AltIntAngCong;
    ¬Collinear E A B ∧ ¬Collinear C B A     [EABncol] by fol t_line Distinct NonCollinearRaa CollinearSymmetry;
    B ∉ l ∧ A ∉ m     [notAmBl] by fol l_line m_line Collinear_DEF - ∉;
    assume ¬(l ∥ m)     [Con] by fol -;
    ¬(l ∩ m = ∅)     [] by fol - l_line m_line PARALLEL;
    consider G such that
    G ∈ l ∧ G ∈ m     [Glm] by fol - MEMBER_NOT_EMPTY IN_INTER;
    ¬(G = A) ∧ ¬(G = B) ∧ Collinear B G C ∧ Collinear B C G ∧ Collinear A E G ∧ Collinear A G E     [GnotAB] by fol - notAmBl ∉ m_line l_line Collinear_DEF;
    ¬Collinear A G B ∧ ¬Collinear B G A ∧ G ∉ t      [AGBncol]  by fol EABncol CollinearSymmetry - NoncollinearityExtendsToLine t_line Collinear_DEF ∉;
    ¬(E,C same_side t)     [Ensim_tC] by fol t_line - Distinct Cnsim_tE SameSideSymmetric;
    E ∈ l ━ {A}  ∧  G ∈ l ━ {A}     [] by fol l_line Glm Distinct GnotAB IN_DIFF IN_SING;
    ¬(G,E same_side t)     []
    proof
      assume G,E same_side t     [Gsim_tE] by fol -;
      A ∉ Open (G, E)     [notGAE] by fol t_line - SameSide_DEF ∉;
      G ∈ ray A E ━ {A}     [] by fol Distinct GnotAB notGAE IN_Ray GnotAB IN_DIFF IN_SING;
      ray A G = ray A E     [rAGrAE] by fol Distinct - RayWellDefined;
      ¬(C,G same_side t)     [Cnsim_tG] by fol t_line AGBncol Distinct Gsim_tE Cnsim_tE SameSideTransitive;
      C ∉ ray B G     [notCrBG] by fol - IN_Ray Distinct t_line AGBncol RaySameSide Cnsim_tG IN_DIFF IN_SING ∉;
      B ∈ Open (C, G)     [] by fol - GnotAB ∉ IN_Ray;
      ∡ G A B <_ang ∡ C B A     [] by fol AGBncol notCrBG - B1' EuclidPropositionI_16;
      ∡ E A B <_ang ∡ C B A     [] by fol - rAGrAE Angle_DEF;
      fol EABncol ANGLE AltIntAngCong - AngleTrichotomy1;
    qed;
    G,C same_side t     [Gsim_tC] by fol t_line AGBncol Distinct - Cnsim_tE AtMost2Sides;
    B ∉ Open (G, C)     [notGBC] by fol t_line - SameSide_DEF ∉;
    G ∈ ray B C ━ {B}     [] by fol Distinct GnotAB notGBC IN_Ray GnotAB IN_DIFF IN_SING;
    ray B G = ray B C     [rBGrBC] by fol Distinct - RayWellDefined;
    ∡ C B A ≡ ∡ E A B     [flipAltIntAngCong] by fol EABncol ANGLE AltIntAngCong C5Symmetric;
    ¬(E,G same_side t)     [Ensim_tG] by fol t_line AGBncol Distinct Gsim_tC Ensim_tC SameSideTransitive;
    E ∉ ray A G     [notErAG] by fol - IN_Ray Distinct t_line AGBncol RaySameSide Ensim_tG IN_DIFF IN_SING ∉;
    A ∈ Open (E, G)     [] by fol - GnotAB ∉ IN_Ray;
    ∡ G B A <_ang ∡ E A B     [] by fol AGBncol notErAG - B1' EuclidPropositionI_16;
    ∡ C B A <_ang ∡ E A B     [] by fol - rBGrBC Angle_DEF;
    fol EABncol ANGLE flipAltIntAngCong - AngleTrichotomy1;
  qed;
`;;

let EuclidPropositionI_28 = theorem `;
  ∀A B C D E F G H l m t.  Line l ∧ A ∈ l ∧ B ∈ l ∧ G ∈ l  ⇒
    Line m ∧ C ∈ m ∧ D ∈ m ∧ H ∈ m  ⇒
    Line t ∧ G ∈ t ∧ H ∈ t  ⇒
    G ∉ m ∧ H ∉ l  ⇒
    G ∈ Open (A, B)  ∧ H ∈ Open (C, D)  ⇒
    G ∈ Open (E, H)  ∧  H ∈ Open (F, G)  ⇒
    ¬(D,A same_side t)  ⇒
    ∡ E G B ≡ ∡ G H D  ∨  ∡ B G H suppl ∡ G H D
    ⇒  l ∥ m

  proof
    intro_TAC ∀A B C D E F G H l m t, l_line, m_line, t_line, notGmHl, H1, H2, H3, H4;
    ¬(A = G) ∧ ¬(G = B) ∧ ¬(H = D) ∧ ¬(E = G) ∧ ¬(G = H) ∧ Collinear A G B ∧ Collinear E G H     [Distinct] by fol H1 H2 B1';
    ¬Collinear H G A ∧ ¬Collinear G H D ∧ A ∉ t ∧ D ∉ t     [HGAncol] by fol Distinct l_line m_line notGmHl NonCollinearRaa CollinearSymmetry Collinear_DEF t_line ∉;
    ¬Collinear B G H ∧ ¬Collinear A G E ∧ ¬Collinear E G B     [BGHncol] by fol - Distinct CollinearSymmetry NoncollinearityExtendsToLine;
    ∡ A G H ≡ ∡ D H G     []
    proof
      case_split EGBeqGHD | BGHeqGHD     by fol H4;
      suppose ∡ E G B ≡ ∡ G H D;
        ∡ E G B ≡ ∡ H G A  ∧
        Angle (∡ E G B)  ∧  Angle (∡ H G A)  ∧  Angle (∡ G H D)      [boo] by fol BGHncol H1 H2 VerticalAnglesCong HGAncol ANGLE;
        ∡ H G A ≡ ∡ E G B     [] by fol - C5Symmetric;
        ∡ H G A ≡ ∡ G H D     [] by fol boo - EGBeqGHD C5Transitive;
        fol - AngleSymmetry;
      end;
      suppose ∡ B G H suppl ∡ G H D;
        ∡ B G H suppl ∡ H G A     [] by fol BGHncol H1 B1' SupplementaryAngles_DEF;
        fol - BGHeqGHD AngleSymmetry SupplementUnique AngleSymmetry;
      end;
    qed;
    fol l_line m_line t_line Distinct HGAncol H3 -  AlternateInteriorAngles;
  qed;
`;;

let OppositeSidesCongImpliesParallelogram = theorem `;
  ∀A B C D.  Quadrilateral A B C D  ⇒
    seg A B ≡ seg C D  ∧  seg B C ≡ seg D A
    ⇒  Parallelogram A B C D

  proof
    intro_TAC ∀A B C D, H1, H2;
    ¬(A = B) ∧ ¬(A = C) ∧ ¬(A = D) ∧ ¬(B = C) ∧ ¬(B = D) ∧ ¬(C = D) ∧
    ¬Collinear A B C ∧ ¬Collinear B C D ∧ ¬Collinear C D A ∧ ¬Collinear D A B     [TetraABCD] by fol H1 Quadrilateral_DEF Tetralateral_DEF;
    consider a c such that
    Line a ∧ A ∈ a ∧ B ∈ a   ∧
    Line c ∧ C ∈ c ∧ D ∈ c     [ac_line] by fol TetraABCD I1;
    consider b d such that
    Line b ∧ B ∈ b ∧ C ∈ b   ∧
    Line d ∧ D ∈ d ∧ A ∈ d     [bd_line] by fol TetraABCD I1;
    consider l such that
    Line l ∧ A ∈ l ∧ C ∈ l     [l_line] by fol TetraABCD I1;
    consider m such that
    Line m ∧ B ∈ m ∧ D ∈ m     [m_line] by fol TetraABCD I1;
    B ∉ l ∧ D ∉ l ∧ A ∉ m  ∧ C ∉ m     [notBDlACm] by fol l_line m_line TetraABCD Collinear_DEF ∉;
    seg A C ≡ seg C A  ∧  seg B D ≡ seg D B     [seg_refl] by fol TetraABCD SEGMENT C2Reflexive SegmentSymmetry;
    A,B,C ≅ C,D,A     [] by fol TetraABCD H2 - SSS;
    ∡ B C A ≡ ∡ D A C  ∧  ∡ C A B ≡ ∡ A C D     [BCAeqDAC] by fol - TriangleCong_DEF;
    seg C D ≡ seg A B     [CDeqAB] by fol TetraABCD SEGMENT H2 C2Symmetric;
    B,C,D ≅ D,A,B     [] by fol TetraABCD H2 - seg_refl SSS;
    ∡ C D B ≡ ∡ A B D  ∧  ∡ D B C ≡ ∡ B D A  ∧  ∡ C B D ≡ ∡ A D B     [CDBeqABD] by fol - TriangleCong_DEF AngleSymmetry;
    ¬(B,D same_side l)  ∨  ¬(A,C same_side m)     [] by fol H1 l_line m_line FiveChoicesQuadrilateral;
    case_split Case1 | Ansim_mC     by fol -;
    suppose ¬(B,D same_side l);
      ¬(D,B same_side l)     [] by fol l_line notBDlACm - SameSideSymmetric;
      a ∥ c  ∧  b ∥ d     [] by fol ac_line l_line TetraABCD notBDlACm - BCAeqDAC AngleSymmetry AlternateInteriorAngles bd_line BCAeqDAC;
      fol H1 ac_line bd_line - Parallelogram_DEF;
    end;
    suppose ¬(A,C same_side m);
      b ∥ d     [b∥d] by fol bd_line m_line TetraABCD notBDlACm - CDBeqABD  AlternateInteriorAngles;
      c ∥ a     [] by fol ac_line m_line TetraABCD notBDlACm Ansim_mC CDBeqABD AlternateInteriorAngles;
      fol H1 ac_line bd_line b∥d - ParallelSymmetry Parallelogram_DEF;
    end;
  qed;
`;;

let OppositeAnglesCongImpliesParallelogramHelp = theorem `;
  ∀A B C D a c.  Quadrilateral A B C D  ⇒
    ∡ A B C ≡ ∡ C D A  ∧  ∡ D A B ≡ ∡ B C D  ⇒
    Line a ∧ A ∈ a ∧ B ∈ a  ⇒  Line c  ∧ C ∈ c ∧ D ∈ c
    ⇒  a ∥ c

  proof
    intro_TAC ∀A B C D a c, H1, H2, a_line, c_line;
    ¬(A = B) ∧ ¬(A = C) ∧ ¬(A = D) ∧ ¬(B = C) ∧ ¬(B = D) ∧ ¬(C = D) ∧
    ¬Collinear A B C ∧ ¬Collinear B C D ∧ ¬Collinear C D A ∧ ¬Collinear D A B     [TetraABCD] by fol H1 Quadrilateral_DEF Tetralateral_DEF;
    ∡ C D A ≡ ∡ A B C  ∧  ∡ B C D ≡ ∡ D A B     [H2'] by fol TetraABCD ANGLE H2 C5Symmetric;
    consider l m such that
    Line l ∧ A ∈ l ∧ C ∈ l  ∧
    Line m ∧ B ∈ m ∧ D ∈ m     [lm_line] by fol TetraABCD I1;
    consider b d such that
    Line b ∧ B ∈ b ∧ C ∈ b   ∧  Line d ∧ D ∈ d ∧ A ∈ d     [bd_line] by fol TetraABCD I1;
    A ∉ c ∧ B ∉ c ∧ A ∉ b ∧ D ∉ b ∧ B ∉ d ∧ C ∉ d     [point_off_line] by fol c_line bd_line Collinear_DEF TetraABCD ∉;
    ¬(A ∈ int_triangle B C D  ∨  B ∈ int_triangle C D A  ∨
    C ∈ int_triangle D A B  ∨  D ∈ int_triangle A B C)     []
    proof
      assume A ∈ int_triangle B C D  ∨  B ∈ int_triangle C D A  ∨
      C ∈ int_triangle D A B  ∨  D ∈ int_triangle A B C     [Con] by fol -;
      ∡ B C D <_ang ∡ D A B  ∨  ∡ C D A <_ang ∡ A B C  ∨
      ∡ D A B <_ang ∡ B C D  ∨  ∡ A B C <_ang ∡ C D A     [] by fol TetraABCD - EuclidPropositionI_21;
      fol - H2' H2 AngleTrichotomy1;
    qed;
    ConvexQuadrilateral A B C D     [] by fol H1 lm_line - FiveChoicesQuadrilateral;
    A ∈ int_angle B C D  ∧  B ∈ int_angle C D A  ∧
    C ∈ int_angle D A B  ∧  D ∈ int_angle A B C     [AintBCD] by fol - ConvexQuad_DEF;
    B,A same_side c  ∧  B,C same_side d     [Bsim_cA] by fol c_line bd_line - InteriorUse;
    A,D same_side b     [Asim_bD] by fol bd_line c_line AintBCD InteriorUse;
    assume ¬(a ∥ c)     [Con] by fol -;
    consider G such that
    G ∈ a ∧ G ∈ c     [Gac] by fol - a_line c_line PARALLEL MEMBER_NOT_EMPTY IN_INTER;
    Collinear A B G ∧ Collinear D G C ∧ Collinear C G D     [ABGcol] by fol a_line - Collinear_DEF c_line;
    ¬(G = A) ∧ ¬(G = B) ∧ ¬(G = C) ∧ ¬(G = D)     [GnotABCD] by fol Gac ABGcol TetraABCD CollinearSymmetry Collinear_DEF;
    ¬Collinear B G C ∧ ¬Collinear A D G     [BGCncol] by fol c_line Gac GnotABCD point_off_line NonCollinearRaa CollinearSymmetry;
    ¬Collinear B C G ∧ ¬Collinear G B C ∧ ¬Collinear G A D ∧ ¬Collinear A G D     [BCGncol] by fol - CollinearSymmetry;
    G ∉ b ∧ G ∉ d     [notGb] by fol bd_line Collinear_DEF BGCncol ∉;
    G ∉ Open (B, A)     [notBGA] by fol Bsim_cA Gac SameSide_DEF ∉;
    B ∉ Open (A, G)     [notABG]
    proof
      assume ¬(B ∉ Open (A, G))     [Con] by fol -;
      B ∈ Open (A, G)     [ABG] by fol - ∉;
      ray A B = ray A G     [rABrAG] by fol - IntervalRay;
      ¬(A,G same_side b)     [] by fol bd_line ABG SameSide_DEF;
      ¬(D,G same_side b)     [] by fol bd_line point_off_line notGb Asim_bD - SameSideTransitive;
      D ∉ ray C G     [] by fol bd_line notGb - RaySameSide TetraABCD IN_DIFF IN_SING ∉;
      C ∈ Open (D, G)     [DCG] by fol GnotABCD ABGcol - IN_Ray ∉;
      consider M such that
      D ∈ Open (C, M)     [CDM] by fol TetraABCD B2';
      D ∈ Open (G, M)     [GDM] by fol - B1' DCG TransitivityBetweennessHelp;
      ∡ C D A suppl ∡ A D M  ∧  ∡ A B C suppl ∡ C B G     [] by fol TetraABCD CDM ABG SupplementaryAngles_DEF;
      ∡ M D A ≡ ∡ G B C     [MDAeqGBC] by fol - H2' SupplementsCongAnglesCong AngleSymmetry;
      ∡ G A D <_ang ∡ M D A  ∧  ∡ G B C <_ang ∡ D C B     [] by fol BCGncol BGCncol GDM DCG B1' EuclidPropositionI_16;
      ∡ G A D <_ang ∡ D C B     [] by fol  - BCGncol ANGLE MDAeqGBC AngleTrichotomy2 AngleOrderTransitivity;
      ∡ D A B <_ang ∡ B C D     [] by fol - rABrAG Angle_DEF AngleSymmetry;
      fol - H2 AngleTrichotomy1;
    qed;
    A ∉ Open (G, B)     []
    proof
      assume ¬(A ∉ Open (G, B))     [Con] by fol -;
      A ∈ Open (B, G)     [BAG] by fol - B1' ∉;
      ray B A = ray B G     [rBArBG] by fol - IntervalRay;
      ¬(B,G same_side d)     [] by fol bd_line BAG SameSide_DEF;
      ¬(C,G same_side d)     [] by fol bd_line point_off_line notGb Bsim_cA -  SameSideTransitive;
      C ∉ ray D G     [] by fol bd_line notGb - RaySameSide TetraABCD IN_DIFF IN_SING ∉;
      D ∈ Open (C, G)     [CDG] by fol GnotABCD ABGcol - IN_Ray ∉;
      consider M such that
      C ∈ Open (D, M)     [DCM] by fol B2' TetraABCD;
      C ∈ Open (G, M)     [GCM] by fol - B1' CDG TransitivityBetweennessHelp;
      ∡ B C D suppl ∡ M C B  ∧  ∡ D A B suppl ∡ G A D     [] by fol TetraABCD CollinearSymmetry DCM BAG SupplementaryAngles_DEF AngleSymmetry;
      ∡ M C B ≡ ∡ G A D     [GADeqMCB] by fol - H2' SupplementsCongAnglesCong;
      ∡ G B C <_ang ∡ M C B  ∧  ∡ G A D <_ang ∡ C D A     [] by fol BGCncol GCM BCGncol CDG B1' EuclidPropositionI_16;
      ∡ G B C <_ang ∡ C D A     [] by fol - BCGncol ANGLE GADeqMCB AngleTrichotomy2 AngleOrderTransitivity;
      ∡ A B C <_ang ∡ C D A     [] by fol - rBArBG Angle_DEF;
      fol - H2 AngleTrichotomy1;
    qed;
    fol TetraABCD GnotABCD ABGcol notABG notBGA - B3' ∉;
  qed;
`;;

let OppositeAnglesCongImpliesParallelogram = theorem `;
  ∀A B C D. Quadrilateral A B C D  ⇒
    ∡ A B C ≡ ∡ C D A  ∧  ∡ D A B ≡ ∡ B C D
    ⇒  Parallelogram A B C D

  proof
    intro_TAC ∀A B C D, H1, H2;
    Quadrilateral B C D A     [QuadBCDA] by fol H1 QuadrilateralSymmetry;
    ¬(A = B) ∧ ¬(B = C) ∧ ¬(C = D) ∧ ¬(D = A) ∧ ¬Collinear B C D ∧ ¬Collinear D A B     [TetraABCD] by fol H1 Quadrilateral_DEF Tetralateral_DEF;
    ∡ B C D ≡ ∡ D A B     [H2'] by fol TetraABCD ANGLE H2 C5Symmetric;
    consider a such that
    Line a ∧ A ∈ a ∧ B ∈ a     [a_line] by fol TetraABCD I1;
    consider b such that
    Line b ∧ B ∈ b ∧ C ∈ b     [b_line] by fol TetraABCD I1;
    consider c such that
    Line c  ∧ C ∈ c ∧ D ∈ c     [c_line] by fol TetraABCD I1;
    consider d such that
    Line d ∧ D ∈ d ∧ A ∈ d     [d_line] by fol TetraABCD I1;
    fol H1 QuadBCDA H2 H2' a_line b_line c_line d_line OppositeAnglesCongImpliesParallelogramHelp Parallelogram_DEF;
  qed;
`;;

let P = NewAxiom
  `;∀P l. Line l ∧ P ∉ l  ⇒ ∃! m. Line m ∧ P ∈ m ∧ m ∥ l`;;

NewConstant("μ",`:(point->bool)->real`);;

let AMa = NewAxiom
 `;∀α. Angle α  ⇒  &0 < μ α ∧ μ α < &180`;;

let AMb = NewAxiom
 `;∀α. Right α  ⇒  μ α  = &90`;;

let AMc = NewAxiom
 `;∀α β. Angle α ∧ Angle β ∧ α ≡ β  ⇒  μ α = μ β`;;

let AMd = NewAxiom
 `;∀A O B P. P ∈ int_angle A O B  ⇒  μ (∡ A O B) = μ (∡ A O P) + μ (∡ P O B)`;;

let ConverseAlternateInteriorAngles = theorem `;
  ∀A B C E l m.  Line l ∧ A ∈ l ∧ E ∈ l  ⇒
    Line m ∧ B ∈ m ∧ C ∈ m  ⇒ Line t ∧ A ∈ t ∧ B ∈ t  ⇒
    ¬(A = E) ∧ ¬(B = C) ∧ ¬(A = B) ∧ E ∉ t ∧ C ∉ t  ⇒
    ¬(C,E same_side t)  ⇒  l ∥ m
    ⇒  ∡ E A B ≡ ∡ C B A

  proof
    intro_TAC ∀A B C E l m, l_line, m_line, t_line, Distinct, Cnsim_tE, para_lm;
    ¬Collinear C B A     [] by fol Distinct t_line NonCollinearRaa CollinearSymmetry;
    A ∉ m ∧ Angle (∡ C B A)     [notAm] by fol m_line - Collinear_DEF ∉ ANGLE;
    consider D such that
    ¬(A = D) ∧ D ∉ t ∧ ¬(C,D same_side t) ∧ seg A D ≡ seg A E  ∧  ∡ B A D ≡ ∡ C B A     [Dexists] by simplify C4OppositeSide -  Distinct t_line;
    consider k such that
    Line k ∧ A ∈ k ∧ D ∈ k     [k_line] by fol Distinct I1;
    k ∥ m     [] by fol - m_line t_line Dexists Distinct AngleSymmetry AlternateInteriorAngles;
    k = l     [] by fol m_line notAm l_line k_line - para_lm P;
    D,E same_side t  ∧  A ∉ Open (D, E)  ∧  Collinear A E D     [] by fol t_line Distinct Dexists Cnsim_tE AtMost2Sides SameSide_DEF ∉ - k_line l_line Collinear_DEF;
    ray A D = ray A E     [] by fol Distinct - IN_Ray Dexists RayWellDefined IN_DIFF IN_SING;
    fol - Dexists AngleSymmetry Angle_DEF;
  qed;
`;;

let HilbertTriangleSum = theorem `;
  ∀A B C.  ¬Collinear A B C
    ⇒  ∃E F. B ∈ Open (E, F)  ∧  C ∈ int_angle A B F  ∧
           ∡ E B A ≡ ∡ C A B  ∧  ∡ C B F ≡ ∡ B C A

  proof
    intro_TAC ∀A B C, ABCncol;
    ¬(A = B) ∧ ¬(A = C) ∧ ¬(B = C) ∧ ¬Collinear C A B     [Distinct] by fol ABCncol NonCollinearImpliesDistinct CollinearSymmetry;
    consider l such that
    Line l ∧ A ∈ l ∧ C ∈ l     [l_line] by fol Distinct I1;
    consider x such that
    Line x ∧ A ∈ x ∧ B ∈ x     [x_line] by fol Distinct I1;
    consider y such that
    Line y ∧ B ∈ y ∧ C ∈ y     [y_line] by fol Distinct I1;
    C ∉ x     [notCx] by fol x_line ABCncol Collinear_DEF ∉;
    Angle (∡ C A B)     [] by fol ABCncol CollinearSymmetry ANGLE;
    consider E such that
    ¬(B = E) ∧ E ∉ x ∧ ¬(C,E same_side x) ∧ seg B E ≡ seg A B ∧ ∡ A B E ≡ ∡ C A B     [Eexists] by simplify C4OppositeSide - Distinct x_line notCx;
    consider m such that
    Line m ∧ B ∈ m ∧ E ∈ m     [m_line] by fol - I1;
    ∡ E B A ≡ ∡ C A B     [EBAeqCAB] by fol Eexists AngleSymmetry;
    m ∥ l     [para_lm] by fol m_line l_line x_line Eexists Distinct notCx - AlternateInteriorAngles;
    m ∩ l = ∅     [ml0] by fol - PARALLEL;
    C ∉ m ∧ A ∉ m     [notACm] by fol - l_line INTER_COMM DisjointOneNotOther;
    consider F such that
    B ∈ Open (E, F)     [EBF] by fol Eexists B2';
    ¬(B = F) ∧ F ∈ m     [EBF'] by fol - B1' m_line BetweenLinear;
    ¬Collinear A B F ∧ F ∉ x      [ABFncol] by fol EBF' m_line notACm NonCollinearRaa CollinearSymmetry Collinear_DEF x_line ∉;
    ¬(E,F same_side x) ∧ ¬(E,F same_side y)     [Ensim_yF] by fol EBF x_line y_line SameSide_DEF;
    C,F same_side x     [Csim_xF] by fol x_line notCx Eexists ABFncol Eexists - AtMost2Sides;
    C,A same_side m     [] by fol m_line l_line ml0 DisjointLinesImplySameSide;
    C ∈ int_angle A B F     [CintABF] by fol ABFncol x_line m_line EBF' notCx notACm Csim_xF - IN_InteriorAngle;
    A ∈ int_angle C B E     [] by fol EBF B1' - InteriorAngleSymmetry InteriorReflectionInterior;
    A ∉ y  ∧  A,E same_side y     [Asim_yE] by fol y_line m_line - InteriorUse;
    E ∉ y ∧ F ∉ y     [notEFy] by fol y_line m_line EBF' Eexists EBF' I1 Collinear_DEF notACm ∉;
    E,A same_side y     [] by fol y_line - Asim_yE SameSideSymmetric;
    ¬(A,F same_side y)     [Ansim_yF] by fol y_line notEFy Asim_yE - Ensim_yF SameSideTransitive;
    ∡ F B C ≡ ∡ A C B     [] by fol m_line EBF' l_line y_line EBF' Distinct notEFy Asim_yE Ansim_yF para_lm ConverseAlternateInteriorAngles;
    fol EBF CintABF EBAeqCAB - AngleSymmetry;
  qed;
`;;

let EuclidPropositionI_13 = theorem `;
  ∀A O B A'.  ¬Collinear A O B  ∧  O ∈ Open (A, A')
    ⇒  μ (∡ A O B) + μ (∡ B O A') = &180

  proof
    intro_TAC ∀A O B A', H1 H2;
    case_split RightAOB | notRightAOB     by fol -;
    suppose Right (∡ A O B);
      Right (∡ B O A')  ∧  μ (∡ A O B) = &90  ∧  μ (∡ B O A') = &90     [] by fol H1 H2 - RightImpliesSupplRight AMb;
      real_arithmetic -;
    end;
    suppose ¬Right (∡ A O B);
      ¬(A = O) ∧ ¬(O = B)     [Distinct] by fol H1 NonCollinearImpliesDistinct;
      consider l such that
      Line l ∧ O ∈ l ∧ A ∈ l ∧ A' ∈ l     [l_line] by fol - I1 H2 BetweenLinear;
      B ∉ l     [notBl] by fol - Distinct I1 Collinear_DEF H1 ∉;
      consider F such that
      Right (∡ O A F)  ∧  Angle (∡ O A F)     [RightOAF] by fol Distinct EuclidPropositionI_11 RightImpliesAngle;
      ∃! r. Ray r ∧ ∃E. ¬(O = E) ∧ r = ray O E ∧ E ∉ l ∧ E,B same_side l ∧ ∡ A O E ≡ ∡ O A F     [] by simplify C4 - Distinct l_line notBl;
      consider E such that
      ¬(O = E)  ∧  E ∉ l  ∧  E,B same_side l  ∧  ∡ A O E ≡ ∡ O A F     [Eexists] by fol -;
      ¬Collinear A O E     [AOEncol] by fol Distinct l_line - NonCollinearRaa CollinearSymmetry;
      Right (∡ A O E)     [RightAOE] by fol - ANGLE RightOAF Eexists CongRightImpliesRight;
      Right (∡ E O A')  ∧  μ (∡ A O E) = &90  ∧  μ (∡ E O A') = &90     [RightEOA'] by fol AOEncol H2 -  RightImpliesSupplRight AMb;
      ¬(∡ A O B ≡ ∡ A O E)     [] by fol notRightAOB H1 ANGLE RightAOE CongRightImpliesRight;
      ¬(∡ A O B = ∡ A O E)     [] by fol H1 AOEncol ANGLE - C5Reflexive;
      ¬(ray O B = ray O E)     [] by fol - Angle_DEF;
      B ∉ ray O E  ∧  O ∉ Open (B, E)     [] by fol Distinct - Eexists RayWellDefined IN_DIFF IN_SING ∉ l_line B1' SameSide_DEF;
      ¬Collinear O E B     [] by fol - Eexists IN_Ray ∉;
      E ∈ int_angle A O B  ∨  B ∈ int_angle A O E     [] by fol Distinct l_line Eexists notBl AngleOrdering - CollinearSymmetry InteriorAngleSymmetry;
      case_split EintAOB | BintAOE     by fol -;
      suppose E ∈ int_angle A O B;
        B ∈ int_angle E O A'     [] by fol H2 - InteriorReflectionInterior;
        μ (∡ A O B) = μ (∡ A O E) + μ (∡ E O B)  ∧
        μ (∡ E O A') = μ (∡ E O B) + μ (∡ B O A')     [] by fol EintAOB - AMd;
        real_arithmetic - RightEOA';
      end;
      suppose B ∈ int_angle A O E;
        E ∈ int_angle B O A'     [] by fol H2 - InteriorReflectionInterior;
        μ (∡ A O E) = μ (∡ A O B) + μ (∡ B O E)  ∧
        μ (∡ B O A') = μ (∡ B O E) + μ (∡ E O A')     [] by fol BintAOE - AMd;
        real_arithmetic - RightEOA';
      end;
    end;
  qed;
`;;

let TriangleSum = theorem `;
  ∀A B C. ¬Collinear A B C
    ⇒  μ (∡ A B C) + μ (∡ B C A) + μ (∡ C A B) = &180

  proof
    intro_TAC ∀A B C, ABCncol;
    ¬Collinear C A B  ∧  ¬Collinear B C A     [CABncol] by fol ABCncol CollinearSymmetry;
    consider E F such that
    B ∈ Open (E, F)  ∧  C ∈ int_angle A B F  ∧  ∡ E B A ≡ ∡ C A B  ∧  ∡ C B F ≡ ∡ B C A     [EBF] by fol ABCncol HilbertTriangleSum;
    ¬Collinear C B F  ∧  ¬Collinear A B F  ∧  Collinear E B F  ∧  ¬(B = E)     [CBFncol] by fol - InteriorAngleSymmetry InteriorEZHelp IN_InteriorAngle B1' CollinearSymmetry;
    ¬Collinear E B A     [EBAncol] by fol CollinearSymmetry - NoncollinearityExtendsToLine;
    μ (∡ A B F) = μ (∡ A B C) + μ (∡ C B F)     [μCintABF] by fol EBF AMd;
    μ (∡ E B A) + μ (∡ A B F) = &180     [suppl180] by fol EBAncol EBF EuclidPropositionI_13;
    μ (∡ C A B) = μ (∡ E B A)  ∧  μ (∡ B C A) = μ (∡ C B F)     [] by fol CABncol EBAncol CBFncol ANGLE EBF AMc;
    real_arithmetic suppl180 μCintABF -;
  qed;
`;;

let CircleConvex2_THM = theorem `;
  ∀O A B C. ¬Collinear A O B  ⇒  B ∈ Open (A, C)  ⇒
    seg O A <__ seg O B  ∨  seg O A ≡ seg O B
    ⇒  seg O B <__ seg O C

  proof
    intro_TAC ∀O A B C, H1, H2, H3;
    ¬Collinear O B A ∧ ¬Collinear B O A ∧ ¬Collinear O A B ∧ ¬(O = A) ∧ ¬(O = B)     [H1'] by fol H1 CollinearSymmetry NonCollinearImpliesDistinct;
    B ∈ Open (C, A) ∧ ¬(C = A) ∧ ¬(C = B) ∧ Collinear A B C ∧ Collinear B A C     [H2'] by fol H2 B1' CollinearSymmetry;
    ¬Collinear O B C ∧ ¬Collinear O C B     [OBCncol] by fol H1' - NoncollinearityExtendsToLine CollinearSymmetry;
    ¬Collinear O A C     [OABncol] by fol H1' H2' NoncollinearityExtendsToLine;
    ∡ O C B <_ang ∡ O B A     [OCBlessOBA] by fol OBCncol H2' ExteriorAngle;
    ∡ O A B <_ang ∡ O B C     [OABlessOBC] by fol H1' H2 ExteriorAngle;
    ∡ O B A <_ang ∡ B A O  ∨  ∡ O B A ≡ ∡ B A O     []
    proof
      assume seg O A ≡ seg O B [Cong]     by fol H3 H1' - EuclidPropositionI_18;
      seg O B ≡ seg O A     [] by fol H1' SEGMENT - C2Symmetric;
      fol H1' - IsoscelesCongBaseAngles AngleSymmetry;
    qed;
    ∡ O B A <_ang ∡ O A B  ∨  ∡ O B A ≡ ∡ O A B     [OBAlessOAB] by fol - AngleSymmetry;
    ∡ O C B <_ang ∡ O B C     [] by fol OCBlessOBA - OABlessOBC OBCncol H1' OABncol OBCncol ANGLE - AngleOrderTransitivity AngleTrichotomy2;
    fol OBCncol - AngleSymmetry EuclidPropositionI_19;
  qed;
`;;
