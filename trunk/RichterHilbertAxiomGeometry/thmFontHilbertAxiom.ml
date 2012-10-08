cd $HOLLIGHT_DIR
ocaml
#use "hol.ml";;

#load "unix.cma";;
loadt "miz3/miz3.ml";;

reset_miz3 0;;

Theorem/Proof template:

let _THM = thm `;
  let
  let
  assume
  assume
  thus

  proof

  qed     by -;
`;;


∉     |- ∀ a l. a ∉ l ⇔ ¬(a ∈ l)

Interval_DEF     |- ∀ A B X. open (A,B) = {X | Between A X B}

Collinear_DEF
  |- ∀ A B C. Collinear A B C  ⇔  ∃ l. Line l ∧ A ∈ l ∧ B ∈ l ∧ C ∈ l

SameSide_DEF
  |- ∀ l A B. A,B same_side l  ⇔  Line l ∧ ¬ ∃ X. X ∈ l ∧ X ∈ open (A,B)

Ray_DEF     |- ∀ A B. ray A B = 
                 {X | ¬(A = B) ∧ Collinear A B X ∧ A ∉ open (X,B)}

Ordered_DEF
   |- ∀ A C B D.
        ordered A B C D  ⇔
        B ∈ open (A,C) ∧ B ∈ open (A,D) ∧ C ∈ open (A,D) ∧ C ∈ open (B,D)

InteriorAngle_DEF     |- ∀ A O B.
         int_angle A O B =
         {P | ¬Collinear A O B ∧
              ∃ a b.
                   Line a ∧ O ∈ a ∧ A ∈ a ∧
                   Line b ∧ O ∈ b ∧ B ∈ b ∧
                   P ∉ a ∧ P ∉ b ∧
                   P,B same_side a ∧ P,A same_side b}

InteriorTriangle_DEF
  |- ∀ A B C.
        int_triangle A B C =
         {P | P ∈ int_angle A B C ∧
              P ∈ int_angle B C A ∧
              P ∈ int_angle C A B}

Tetralateral_DEF
  |- ∀ C D A B.
       Tetralateral A B C D  ⇔
       ¬(A = B) ∧ ¬(A = C) ∧ ¬(A = D) ∧ ¬(B = C) ∧ ¬(B = D) ∧ ¬(C = D) ∧
       ¬Collinear A B C ∧ ¬Collinear B C D ∧ ¬Collinear C D A ∧ ¬Collinear D A B

Quadrilateral_DEF
  |- ∀ B C D A.
         Quadrilateral A B C D  ⇔
         Tetralateral A B C D ∧
         open (A,B) ∩ open (C,D) = ∅ ∧
         open (B,C) ∩ open (D,A) = ∅

ConvexQuad_DEF
  |- ∀ D A B C.
         ConvexQuadrilateral A B C D ⇔
         Quadrilateral A B C D ∧
         A ∈ int_angle B C D ∧
         B ∈ int_angle C D A ∧
         C ∈ int_angle D A B ∧
         D ∈ int_angle A B C

Segment_DEF     |- ∀ A B. seg A B = {A, B} ∪ open (A,B)

SEGMENT     |- ∀ s. Segment s  ⇔  ∃ A B. s = seg A B ∧ ¬(A = B)

SegmentOrdering_DEF
  |- ∀ t s.
         s <__ t ⇔
         Segment s ∧
         ∃ C D X. t = seg C D  ∧  X ∈ open (C,D)  ∧  s ≡ seg C X

Angle_DEF     |- ∀ A O B. ∡ A O B = ray O A ∪ ray O B

ANGLE
  |- ∀ α. Angle α  ⇔  ∃ A O B. α = ∡ A O B ∧ ¬Collinear A O B

AngleOrdering_DEF
  |- ∀ β α.
         α <_ang β ⇔
         Angle α ∧
         ∃ A O B G.
              ¬Collinear A O B ∧ β = ∡ A O B ∧
              G ∈ int_angle A O B ∧ α ≡ ∡ A O G

RAY     |- ∀ r. Ray r ⇔ (∃O A. ¬(O = A) ∧ r = ray O A)

TriangleCong_DEF
  |- ∀ A B C A' B' C'.
         A,B,C ≅ A',B',C' ⇔
         ¬Collinear A B C ∧ ¬Collinear A' B' C' ∧
         seg A B ≡ seg A' B' ∧ 
         seg A C ≡ seg A' C' ∧
         seg B C ≡ seg B' C' ∧
         ∡ A B C ≡ ∡ A' B' C' ∧
         ∡ B C A ≡ ∡ B' C' A' ∧
         ∡ C A B ≡ ∡ C' A' B'

SupplementaryAngles_DEF
  |- ∀α β.
         α suppl β ⇔
         ∃ A O B A'.
              ¬Collinear A O B ∧ O ∈ open (A,A') ∧
              α = ∡ A O B  ∧  β = ∡ B O A'

RightAngle_DEF
  |- ∀α. Right α ⇔ ∃ β. α suppl β ∧ α ≡ β

PlaneComplement_DEF
  |- ∀ α. complement α = {P | P ∉ α}

CONVEX
  |- ∀α. Convex α ⇔
             ∀ A B. A ∈ α ∧ B ∈ α ⇒ open (A,B) ⊂ α

PARALLEL
  |- ∀ l k. l ∥ k  ⇔  Line l  ∧  Line k  ∧  l ∩ k = ∅

Parallelogram_DEF
  |- ∀ A B C D.
         Parallelogram A B C D  ⇔
         Quadrilateral A B C D ∧
         ∃ a b c d.
              Line a ∧ A ∈ a ∧ B ∈ a ∧ Line b ∧ B ∈ b ∧ C ∈ b ∧
              Line c ∧ C ∈ c ∧ D ∈ d ∧ Line d ∧ D ∈ d ∧ A ∈ d ∧
              a ∥ c  ∧  b ∥ d

I1     |- ∀ A B. ¬(A = B) ⇒ (∃! l. Line l ∧ A ∈ l ∧ B ∈ l)

I2     |- ∀ l. Line l ⇒ (∃ A B. A ∈ l ∧ B ∈ l ∧ ¬(A = B))

I3     |- ∃ A B C. ¬(A = B) ∧ ¬(A = C) ∧ ¬(B = C) ∧ ¬Collinear A B C

B1     |- ∀ A B C.
         Between A B C
         ⇒ ¬(A = B) ∧ ¬(A = C) ∧ ¬(B = C) ∧
             Between C B A ∧ Collinear A B C

B2     |- ∀ A B. ¬(A = B)  ⇒  ∃C. Between A B C

B3     |- ∀ A B C.
         ¬(A = B) ∧ ¬(A = C) ∧ ¬(B = C) ∧ Collinear A B C
         ⇒ (Between A B C ∨ Between B C A ∨ Between C A B) ∧
             ¬(Between A B C ∧ Between B C A) ∧
             ¬(Between A B C ∧ Between C A B) ∧
             ¬(Between B C A ∧ Between C A B)

B4     |- ∀ l A B C.
         Line l ∧
         ¬Collinear A B C ∧
         A ∉ l ∧ B ∉ l ∧ C ∉ l ∧
         (∃X. X ∈ l ∧ Between A X C)
         ⇒ (∃ Y. Y ∈ l ∧ Between A Y B) ∨
             (∃ Y. Y ∈ l ∧ Between B Y C)

C1     |- ∀ s O Z.
         Segment s ∧ ¬(O = Z)
         ⇒ ∃! P. P ∈ ray O Z ━ O  ∧  seg O P ≡ s

C2Reflexive     |- Segment s ⇒ s ≡ s

C2Symmetric     |- Segment s ∧ Segment t ∧ s ≡ t ⇒ t ≡ s

C2Transitive
  |- Segment s ∧ Segment t ∧ Segment u ∧ s ≡ t ∧ t ≡ u ⇒ s ≡ u

C3     |- ∀ A B C A' B' C'.
         B ∈ open (A,C) ∧ B' ∈ open (A',C') ∧
         seg A B ≡ seg A' B' ∧ seg B C ≡ seg B' C'
         ⇒ seg A C ≡ seg A' C'

C4     |- ∀ α O A l Y.
         Angle α ∧ ¬(O = A) ∧ Line l ∧ O ∈ l ∧ A ∈ l ∧ Y ∉ l
         ⇒  ∃! r. Ray r ∧ ∃ B. ¬(O = B) ∧ r = ray O B ∧
                    B ∉ l  ∧ B,Y same_side l ∧ ∡ A O B ≡ α

C5Reflexive     |- Angle α ⇒ α ≡ α

C5Symmetric
  |- Angle α ∧ Angle β ∧ α ≡ β ⇒ β ≡ α

C5Transitive
  |- Angle α ∧ Angle β ∧ Angle γ ∧ α ≡ β ∧ β ≡ γ
     ⇒ α ≡ γ

C6     |- ∀A B C A' B' C'.
         ¬Collinear A B C ∧ ¬Collinear A' B' C' ∧
         seg B A ≡ seg B' A' ∧ seg B C ≡ seg B' C' ∧
         ∡ A B C ≡ ∡ A' B' C'
         ⇒ ∡ B C A ≡ ∡ B' C' A'


IN_Interval     |- ∀ A B X. X ∈ open (A,B) ⇔ Between A X B

IN_Ray     |- ∀ A B X.
         X ∈ ray A B  ⇔  ¬(A = B) ∧ Collinear A B X ∧ A ∉ open (X,B)

IN_InteriorAngle     |- ∀A O B P.
         P ∈ int_angle A O B  ⇔  ¬Collinear A O B ∧  ∃ a b.
         Line a ∧ O ∈ a ∧ A ∈ a ∧ Line b ∧ O ∈ b ∧ B ∈ b ∧
         P ∉ a ∧ P ∉ b ∧ P,B same_side a ∧ P,A same_side b

IN_InteriorTriangle
  |- ∀A B C P.
         P ∈ int_triangle A B C ⇔
         P ∈ int_angle A B C ∧ P ∈ int_angle B C A ∧ P ∈ int_angle C A B

IN_PlaneComplement
  |- ∀α P. P ∈ complement α ⇔ P ∉ α

B1'     |- ∀ A B C.
         B ∈ open (A,C)
         ⇒ ¬(A = B) ∧ ¬(A = C) ∧ ¬(B = C) ∧
             B ∈ open (C,A) ∧ Collinear A B C

B2'     |- ∀ A B. ¬(A = B) ⇒ (∃ C. B ∈ open (A,C))

B3'     |- ∀ A B C.
         ¬(A = B) ∧ ¬(A = C) ∧ ¬(B = C) ∧ Collinear A B C
         ⇒ (B ∈ open (A,C) ∨ C ∈ open (B,A) ∨ A ∈ open (C,B)) ∧
             ¬(B ∈ open (A,C) ∧ C ∈ open (B,A)) ∧
             ¬(B ∈ open (A,C) ∧ A ∈ open (C,B)) ∧
             ¬(C ∈ open (B,A) ∧ A ∈ open (C,B))

B4'     |- ∀ l A B C.
         Line l  ∧  ¬Collinear A B C  ∧  A ∉ l  ∧  B ∉ l  ∧  C ∉ l  ∧
         (∃ X. X ∈ l ∧ X ∈ open (A,C))
         ⇒ (∃ Y. Y ∈ l ∧ Y ∈ open (A,B)) ∨
           (∃ Y. Y ∈ l ∧ Y ∈ open (B,C))

B4''     |- ∀ l A B C.
         Line l  ∧  ¬Collinear A B C  ∧  A ∉ l  ∧  B ∉ l  ∧  C ∉ l  ∧ 
         A,B same_side l  ∧  B,C same_side l
         ⇒ A,C same_side l

DisjointOneNotOther
  |- ∀ l m. (∀x. x ∈ m ⇒ x ∉ l)  ⇔  l ∩ m = ∅

EquivIntersectionHelp
  |- ∀ e x l m.
         (l ∩ m = {x} ∨ m ∩ l = {x})  ∧  e ∈ m ━ x  ⇒  e ∉ l

CollinearSymmetry
  |- ∀ A B C.
         Collinear A B C
         ⇒ Collinear A C B ∧ Collinear B A C ∧
             Collinear B C A ∧ Collinear C A B ∧ Collinear C B A

ExistsNewPointOnLine
  |- ∀ P l. Line l ∧ P ∈ l  ⇒  ∃ Q. Q ∈ l ∧ ¬(P = Q)

ExistsPointOffLine     |- ∀ l. Line l ⇒ ∃ Q. Q ∉ l

BetweenLinear
  |- ∀ A B C m.
         Line m ∧ A ∈ m ∧ C ∈ m ∧ 
         B ∈ open (A,C) ∨ C ∈ open (B,A) ∨ A ∈ open (C,B)
         ⇒ B ∈ m

CollinearLinear
  |- ∀ A B C m.
         Line m ∧ A ∈ m ∧ C ∈ m ∧ ¬(A = C) ∧ 
         Collinear A B C ∨ Collinear B C A ∨ Collinear C A B
         ⇒ B ∈ m

NonCollinearImpliesDistinct
  |- ∀ A B C. ¬Collinear A B C ⇒ ¬(A = B) ∧ ¬(A = C) ∧ ¬(B = C)

Reverse4Order
  |- ∀ A B C D. ordered A B C D ⇒ ordered D C B A

OriginInRay     |- ∀ O Q. ¬(Q = O) ⇒ O ∈ ray O Q

EndpointInRay     |- ∀ O Q. ¬(Q = O) ⇒ Q ∈ ray O Q

I1Uniqueness
  |- ∀ X l m.
         Line l ∧ Line m ∧ ¬(l = m) ∧ X ∈ l ∧ X ∈ m
         ⇒ l ∩ m = {X}

EquivIntersection
  |- ∀ A B X l m.
         Line l  ∧  Line m  ∧  l ∩ m = {X}  ∧  
         A ∈ m ━ X  ∧  B ∈ m ━ X  ∧  X ∉ open (A,B)
         ⇒ A,B same_side l

RayLine
  |- ∀ O P l. Line l ∧ O ∈ l ∧ P ∈ l ⇒ ray O P ⊂ l

RaySameSide
  |- ∀ l O A P.
         Line l  ∧  O ∈ l  ∧  A ∉ l  ∧  P ∈ ray O A ━ O
         ⇒ P ∉ l ∧ P,A same_side l

IntervalRayEZ
  |- ∀ A B C.
         B ∈ open (A,C)  ⇒  B ∈ ray A C ━ A  ∧  C ∈ ray A B ━ A

NoncollinearityExtendsToLine
  |- ∀ A O B X.
         ¬Collinear A O B  ∧  Collinear O B X  ∧  ¬(X = O)
         ⇒ ¬Collinear A O X

SameSideReflexive
  |- ∀ l A. Line l ∧ A ∉ l ⇒ A,A same_side l

SameSideSymmetric
  |- ∀ l A B.
         Line l ∧ A ∉ l ∧ B ∉ l  ∧  A,B same_side l
         ⇒ B,A same_side l

SameSideTransitive
  |- ∀l A B C.
         Line l ∧ A ∉ l ∧ B ∉ l ∧ C ∉ l  ∧ 
         A,B same_side l ∧ B,C same_side l
         ⇒ A,C same_side l

ConverseCrossbar
  |- ∀ O A B G. ¬Collinear A O B  ∧  G ∈ open (A,B)  ⇒  G ∈ int_angle A O B

InteriorUse
  |- ∀ A O B P a b.
         Line a ∧ O ∈ a ∧ A ∈ a  ∧  
         Line b ∧ O ∈ b ∧ B ∈ b  ∧ 
         P ∈ int_angle A O B
         ⇒ P ∉ a ∧ P ∉ b ∧ P,B same_side a ∧ P,A same_side b

InteriorEZHelp
  |- ∀ A O B P.
         P ∈ int_angle A O B
         ⇒ ¬(P = A) ∧ ¬(P = O) ∧ ¬(P = B) ∧ ¬Collinear A O P

InteriorAngleSymmetry
  |- ∀ A O B P. P ∈ int_angle A O B  ⇒  P ∈ int_angle B O A

InteriorWellDefined
  |- ∀ A O B X P.
         P ∈ int_angle A O B  ∧  X ∈ ray O B ━ O  ⇒  P ∈ int_angle A O X

WholeRayInterior
  |- ∀A O B X P.
         X ∈ int_angle A O B  ∧  P ∈ ray O X ━ O
         ⇒ P ∈ int_angle A O B

AngleOrdering
  |- ∀ O A P Q a.
         ¬(O = A)  ∧  Line a ∧ O ∈ a ∧ A ∈ a  ∧ 
         P ∉ a ∧ Q ∉ a ∧ P,Q same_side a ∧ ¬Collinear P O Q
         ⇒ P ∈ int_angle Q O A ∨ Q ∈ int_angle P O A

InteriorsDisjointSupplement
  |- ∀A O B A'.
         ¬Collinear A O B  ∧  O ∈ open (A,A')
         ⇒ int_angle A O B ∩ int_angle B O A' = ∅

InteriorReflectionInterior
  |- ∀ A O B D A'.
         O ∈ open (A,A')  ∧  D ∈ int_angle A O B  ⇒  B ∈ int_angle D O A'

Crossbar_THM
  |- ∀ O A B D.
         D ∈ int_angle A O B
         ⇒ ∃ G. G ∈ open (A,B) ∧ G ∈ ray O D ━ O

InteriorOpposite
  |- ∀ A O B P p.
         P ∈ int_angle A O B  ∧  Line p ∧ O ∈ p ∧ P ∈ p
         ⇒ ¬(A,B same_side p)

AlternateConverseCrossbar
  |- ∀ O A B G. Collinear A G B  ∧  G ∈ int_angle A O B  ⇒  G ∈ open (A,B)

IntervalTransitivity
  |- ∀ O P Q R m.
         Line m  ∧ O ∈ m  ∧ 
         P ∈ m ━ O ∧ Q ∈ m ━ O ∧ R ∈ m ━ O  ∧ 
         O ∉ open (P,Q) ∧ O ∉ open (Q,R)
         ⇒ O ∉ open (P,R)

RayWellDefinedHalfway
  |- ∀ O P Q. ¬(Q = O) ∧ P ∈ ray O Q ━ O  ⇒  ray O P ⊂ ray O Q

RayWellDefined
  |- ∀ O P Q. ¬(Q = O) ∧ P ∈ ray O Q ━ O  ⇒  ray O P = ray O Q

OppositeRaysIntersect1pointHelp
  |- ∀ A O B X.
         O ∈ open (A,B)  ∧  X ∈ ray O B ━ O
         ⇒ X ∉ ray O A  ∧  O ∈ open (X,A)

OppositeRaysIntersect1point
  |- ∀ A O B. O ∈ open (A,B)  ⇒  ray O A ∩ ray O B = {O}

IntervalRay
  |- ∀ A B C. B ∈ open (A,C)  ⇒  ray A B = ray A C

TransitivityBetweennessHelp
  |- ∀ A B C D. B ∈ open (A,C) ∧ C ∈ open (B,D)  ⇒  B ∈ open (A,D)

TransitivityBetweenness
  |- ∀ A B C D. B ∈ open (A,C) ∧ C ∈ open (B,D)  ⇒  ordered A B C D

IntervalsAreConvex
  |- ∀ A B C. B ∈ open (A,C) ⇒ open (A,B) ⊂ open (A,C)

TransitivityBetweennessVariant
  |- ∀ A X B C. X ∈ open (A,B) ∧ B ∈ open (A,C)  ⇒  ordered A X B C

Interval2sides2aLineHelp
  |- ∀ A B C X. B ∈ open (A,C)  ⇒  X ∉ open (A,B) ∨ X ∉ open (B,C)

Interval2sides2aLine
  |- ∀ A B C X. 
         Collinear A B C 
         ⇒ X ∉ open (A,B) ∨ X ∉ open (A,C) ∨ X ∉ open (B,C)

TwosidesTriangle2aLine
  |- ∀A B C Y l m.
         Line l ∧ ¬Collinear A B C ∧ A ∉ l ∧ B ∉ l ∧ C ∉ l  ∧ 
         Line m ∧ A ∈ m ∧ C ∈ m  ∧ 
         Y ∈ l ∧ Y ∈ m  ∧ ¬(A,B same_side l) ∧ ¬(B,C same_side l)
         ⇒ A,C same_side l

LineUnionOf2Rays
  |- ∀ A O B l.
         Line l ∧ A ∈ l ∧ B ∈ l  ∧  O ∈ open (A,B)
         ⇒ l = ray O A ∪ ray O B

AtMost2Sides
  |- ∀ A B C l.
         Line l ∧ A ∉ l ∧ B ∉ l ∧ C ∉ l
         ⇒ A,B same_side l ∨ A,C same_side l ∨ B,C same_side l

FourPointsOrder
  |- ∀ A B C X l.
     Line l ∧ A ∈ l ∧ B ∈ l ∧ C ∈ l ∧ X ∈ l  ∧  B ∈ open (A,C)  ∧ 
     ¬(X = A) ∧ ¬(X = B) ∧ ¬(X = C)
     ⇒ ordered X A B C ∨ ordered A X B C ∨ ordered A B X C ∨ ordered A B C X

HilbertAxiomRedundantByMoore
  |- ∀ A B C D l.
         Line l ∧ A ∈ l ∧ B ∈ l ∧ C ∈ l ∧ D ∈ l  ∧ 
         ¬(A = B) ∧ ¬(A = C) ∧ ¬(A = D) ∧ ¬(B = C) ∧ ¬(B = D) ∧ ¬(C = D)
         ⇒ ordered D A B C ∨ ordered A D B C ∨ ordered A B D C ∨
            ordered A B C D ∨ ordered D A C B ∨ ordered A D C B ∨
            ordered A C D B ∨ ordered A C B D ∨ ordered D C A B ∨
            ordered C D A B ∨ ordered C A D B ∨ ordered C A B D

InteriorTransitivity
  |- ∀A O B F G.
         G ∈ int_angle A O B  ∧  F ∈ int_angle A O G
         ⇒ F ∈ int_angle A O B

HalfPlaneConvexNonempty
  |- ∀l H A.
         Line l  ∧  A ∉ l  ∧  H = {X | X ∉ l ∧ X,A same_side l}
         ⇒ ¬(H = ∅)  ∧  H ⊂ complement l  ∧  Convex H

PlaneSeparation
  |- ∀ l. Line l
         ⇒ ∃ H1 H2.
	       H1 ∩ H2 = ∅  ∧  ¬(H1 = ∅)  ∧  ¬(H2 = ∅) ∧
	       Convex H1  ∧  Convex H2  ∧  complement l = H1 ∪ H2 ∧
	       ∀ P Q. P ∈ H1 ∧ Q ∈ H2  ⇒  ¬(P,Q same_side l)

TetralateralSymmetry
  |- ∀ A B C D.
         Tetralateral A B C D
         ⇒ Tetralateral B C D A ∧ Tetralateral A B D C

EasyEmptyIntersectionsTetralateralHelp
  |- ∀ A B C D. Tetralateral A B C D  ⇒  open (A,B) ∩ open (B,C) = ∅

EasyEmptyIntersectionsTetralateral
  |- ∀ A B C D.
       Tetralateral A B C D
       ⇒ open (A,B) ∩ open (B,C) = ∅  ∧  open (B,C) ∩ open (C,D) = ∅  ∧
          open (C,D) ∩ open (D,A) = ∅  ∧  open (D,A) ∩ open (A,B) = ∅

SegmentSameSideOppositeLine
  |- ∀ A B C D a c.
         Quadrilateral A B C D  ∧ 
         Line a ∧ A ∈ a ∧ B ∈ a  ∧  Line c ∧ C ∈ c ∧ D ∈ c
         ⇒ A,B same_side c  ∨  C,D same_side a

ConvexImpliesQuad
  |- ∀ A B C D.
         Tetralateral A B C D  ∧   
         C ∈ int_angle D A B  ∧  D ∈ int_angle A B C
         ⇒ Quadrilateral A B C D

DiagonalsIntersectImpliesConvexQuad
  |- ∀ A B C D G.
         ¬Collinear B C D  ∧  G ∈ open (A,C)  ∧  G ∈ open (B,D)
         ⇒ ConvexQuadrilateral A B C D

DoubleNotSimImpliesDiagonalsIntersect
  |- ∀ A B C D l m.
         Line l ∧ A ∈ l ∧ C ∈ l  ∧ 
         Line m ∧ B ∈ m ∧ D ∈ m  ∧ 
         Tetralateral A B C D  ∧ 
         ¬(B,D same_side l)  ∧  ¬(A,C same_side m)
         ⇒ (∃ G. G ∈ open (A,C) ∩ open (B,D)) ∧ 
             ConvexQuadrilateral A B C D

ConvexQuadImpliesDiagonalsIntersect
  |- ∀ A B C D l m.
         Line l ∧ A ∈ l ∧ C ∈ l  ∧ 
         Line m ∧ B ∈ m ∧ D ∈ m  ∧ 
         ConvexQuadrilateral A B C D
         ⇒ ¬(B,D same_side l) ∧ ¬(A,C same_side m) ∧
             (∃ G. G ∈ open (A,C) ∩ open (B,D)) ∧
             ¬Quadrilateral A B D C

FourChoicesTetralateralHelp
  |- ∀ A B C D.
         Tetralateral A B C D  ∧  C ∈ int_angle D A B
         ⇒ ConvexQuadrilateral A B C D  ∨  C ∈ int_triangle D A B

InteriorTriangleSymmetry
  |- ∀ A B C P. P ∈ int_triangle A B C  ⇒  P ∈ int_triangle B C A

FourChoicesTetralateral
  |- ∀ A B C D a.
         Tetralateral A B C D  ∧  Line a ∧ A ∈ a ∧ B ∈ a  ∧ 
         C,D same_side a
         ⇒ ConvexQuadrilateral A B C D  ∨  ConvexQuadrilateral A B D C ∨
            D ∈ int_triangle A B C  ∨  C ∈ int_triangle D A B

QuadrilateralSymmetry
  |- ∀ A B C D.
         Quadrilateral A B C D
         ⇒ Quadrilateral B C D A ∧ 
             Quadrilateral C D A B ∧
             Quadrilateral D A B C

FiveChoicesQuadrilateral
  |- ∀ A B C D l m.
         Quadrilateral A B C D  ∧ 
         Line l ∧ A ∈ l ∧ C ∈ l  ∧ 
         Line m ∧ B ∈ m ∧ D ∈ m
         ⇒ (ConvexQuadrilateral A B C D  ∨
              A ∈ int_triangle B C D  ∨  B ∈ int_triangle C D A   ∨
              C ∈ int_triangle D A B  ∨  D ∈ int_triangle A B C)  ∧
            (¬(B,D same_side l) ∨ ¬(A,C same_side m))

IntervalSymmetry     |- ∀ A B. open (A,B) = open (B,A)

SegmentSymmetry     |- ∀ A B. seg A B = seg B A

C1OppositeRay
  |- ∀ O P s.
         Segment s ∧ ¬(O = P)  ⇒  ∃ Q. P ∈ open (O,Q) ∧ seg P Q ≡ s

OrderedCongruentSegments
  |- ∀ A B C D F.
         ¬(A = C) ∧ ¬(D = F)  ∧  seg A C ≡ seg D F  ∧  B ∈ open (A,C)
         ⇒ ∃ E. E ∈ open (D,F)  ∧  seg A B ≡ seg D E

SegmentSubtraction
  |- ∀ A B C A' B' C'.
         B ∈ open (A,C) ∧ B' ∈ open (A',C')  ∧ 
         seg A B ≡ seg A' B'  ∧  seg A C ≡ seg A' C'
         ⇒ seg B C ≡ seg B' C'

SegmentOrderingTransitive
  |- ∀ s t u. s <__ t  ∧  t <__ u  ⇒  s <__ u

SegmentOrderingUse
  |- ∀A B s.
         Segment s  ∧  ¬(A = B)  ∧  s <__ seg A B
         ⇒ ∃ G. G ∈ open (A,B) ∧ s ≡ seg A G

SegmentTrichotomy1     |- ∀ s t. s <__ t  ⇒  ¬(s ≡ t)

SegmentTrichotomy2
  |- ∀ s t u. s <__ t ∧ Segment u ∧ t ≡ u  ⇒  s <__ u

SegmentOrderTransitivity
  |- ∀ s t u. s <__ t ∧ t <__ u  ⇒  s <__ u

SegmentTrichotomy
  |- ∀ s t.
       Segment s ∧ Segment t
       ⇒ (s ≡ t  ∨  s <__ t  ∨  t <__ s) ∧
          ¬(s ≡ t ∧ s <__ t) ∧ ¬(s ≡ t ∧ t <__ s) ∧ ¬(s <__ t ∧ t <__ s)

C4Uniqueness
  |- ∀ O A B P l.
         Line l ∧ O ∈ l ∧ A ∈ l ∧ ¬(O = A)  ∧ 
         B ∉ l ∧ P ∉ l ∧ P,B same_side l  ∧  ∡ A O P ≡ ∡ A O B
         ⇒ ray O B = ray O P

AngleSymmetry     |- ∀ A O B. ∡ A O B = ∡ B O A

TriangleCongSymmetry
  |- ∀ A B C A' B' C'.
         A,B,C ≅ A',B',C'
         ⇒ A,C,B ≅ A',C',B'  ∧  B,A,C ≅ B',A',C'  ∧
            B,C,A ≅ B',C',A'  ∧  C,A,B ≅ C',A',B'  ∧  C,B,A ≅ C',B',A'

SAS
  |- ∀ A B C A' B' C'.
         ¬Collinear A B C ∧ ¬Collinear A' B' C'    ∧ 
         seg B A ≡ seg B' A'  ∧  seg B C ≡ seg B' C'  ∧ 
         ∡ A B C ≡ ∡ A' B' C'
         ⇒ A,B,C ≅ A',B',C'

ASA
  |- ∀ A B C A' B' C'.
         ¬Collinear A B C  ∧  ¬Collinear A' B' C'  ∧  
         seg A C ≡ seg A' C'  ∧ 
         ∡ C A B ≡ ∡ C' A' B'  ∧  ∡ B C A ≡ ∡ B' C' A'
         ⇒ A,B,C ≅ A',B',C'

AngleSubtraction
  |- ∀ A O B A' O' B' G G'.
         G ∈ int_angle A O B  ∧  G' ∈ int_angle A' O' B'  ∧  
         ∡ A O B ≡ ∡ A' O' B'  ∧  ∡ A O G ≡ ∡ A' O' G'
         ⇒ ∡ G O B ≡ ∡ G' O' B'

OrderedCongruentAngles
  |- ∀ A O B A' O' B' G.
         ¬Collinear A' O' B'  ∧ ∡ A O B ≡ ∡ A' O' B'  ∧  
	 G ∈ int_angle A O B
         ⇒ ∃ G'. G' ∈ int_angle A' O' B'  ∧  ∡ A O G ≡ ∡ A' O' G'

AngleAddition
  |- ∀ A O B A' O' B' G G'.
         G ∈ int_angle A O B  ∧  G' ∈ int_angle A' O' B'  ∧
         ∡ A O G ≡ ∡ A' O' G'  ∧  ∡ G O B ≡ ∡ G' O' B'  ∧
         ⇒ ∡ A O B ≡ ∡ A' O' B'

AngleOrderingUse
  |- ∀ A O B α.
         Angle α  ∧  ¬Collinear A O B  ∧  α <_ang ∡ A O B
         ⇒ (∃ G. G ∈ int_angle A O B ∧ α ≡ ∡ A O G)

AngleTrichotomy1
  |- ∀ α β. α <_ang β ⇒ ¬(α ≡ β)

AngleTrichotomy2
  |- ∀ α β γ.
         α <_ang β  ∧  Angle γ  ∧  β ≡ γ
         ⇒ α <_ang γ

AngleOrderTransitivity
  |- ∀α β γ.
         α <_ang β  ∧  β <_ang γ
         ⇒ α <_ang γ

AngleTrichotomy
  |- ∀ α β.
         Angle α ∧ Angle β
         ⇒ (α ≡ β ∨ α <_ang β ∨ β <_ang α) ∧
             ¬(α ≡ β ∧ α <_ang β) ∧
             ¬(α ≡ β ∧ β <_ang α) ∧
             ¬(α <_ang β ∧ β <_ang α)

SupplementExists
  |- ∀ α. Angle α  ⇒  ∃ α'. α suppl α'

SupplementImpliesAngle
  |- ∀ α β. α suppl β  ⇒  Angle α ∧ Angle β

RightImpliesAngle     |- ∀ α. Right α  ⇒  Angle α

SupplementSymmetry
  |- ∀ α β. α suppl β  ⇒  β suppl α

SupplementsCongAnglesCong
  |- ∀ α β α' β'.
         α suppl α'  ∧  β suppl β'  ∧  α ≡ β
         ⇒ α' ≡ β'

SupplementUnique
  |- ∀ α β β'.
         α suppl β  ∧  α suppl β'  ⇒  β ≡ β'

CongRightImpliesRight
  |- ∀ α β.
         Angle α ∧ Right β ∧ α ≡ β  ⇒  Right α

RightAnglesCongruentHelp
  |- ∀ A O B A' P a.
         ¬Collinear A O B  ∧  O ∈ open (A,A')
         Right (∡ A O B)  ∧  Right (∡ A O P)
         ⇒ P ∉ int_angle A O B

RightAnglesCongruent
  |- ∀ α β. Right α ∧ Right β  ⇒  α ≡ β

OppositeRightAnglesLinear
  |- ∀ A B O H h.
         ¬Collinear A O H ∧ ¬Collinear H O B  ∧ 
         Right (∡ A O H) ∧ Right (∡ H O B)  ∧ 
         Line h ∧ O ∈ h ∧ H ∈ h  ∧ ¬(A,B same_side h)
         ⇒ O ∈ open (A,B)

IsoscelesCongBaseAngles
  |- ∀ A B C.
         ¬Collinear A B C  ∧  seg B A ≡ seg B C
         ⇒ ∡ C A B ≡ ∡ A C B

C4withC1
  |- ∀ α l O A Y P Q.
         Angle α ∧ ¬(O = A) ∧ ¬(P = Q)  ∧
         Line l ∧ O ∈ l ∧ A ∈ l  ∧  Y ∉ l
         ⇒ ∃ N. ¬(O = N) ∧ N ∉ l  ∧  N,Y same_side l  ∧
                  seg O N ≡ seg P Q  ∧  ∡ A O N ≡ α

C4OppositeSide
  |- ∀ α l O A Z P Q.
         Angle α ∧ ¬(O = A) ∧ ¬(P = Q)  ∧ 
         Line l ∧ O ∈ l ∧ A ∈ l ∧ Z ∉ l
         ⇒ ∃ N. ¬(O = N) ∧ N ∉ l ∧ ¬(Z,N same_side l) ∧
                 seg O N ≡ seg P Q  ∧  ∡ A O N ≡ α

SSS
  |- ∀ A B C A' B' C'.
     ¬Collinear A B C  ∧  ¬Collinear A' B' C'  ∧
     seg A B ≡ seg A' B'  ∧  seg A C ≡ seg A' C'  ∧  seg B C ≡ seg B' C'
     ⇒ A,B,C ≅ A',B',C'

AngleBisector
  |- ∀ A B C.
         ¬Collinear B A C
         ⇒ ∃ F. F ∈ int_angle B A C  ∧  ∡ B A F ≡ ∡ F A C

EuclidPropositionI_6
  |- ∀ A B C.
         ¬Collinear A B C  ∧  ∡ B A C ≡ ∡ B C A
         ⇒ seg B A ≡ seg B C

IsoscelesExists
  |- ∀ A B. ¬(A = B)  ⇒  ∃ D. ¬Collinear A D B  ∧  seg D A ≡ seg D B

MidpointExists
  |- ∀ A B. ¬(A = B)  ⇒  ∃ M. M ∈ open (A,B) ∧ seg A M ≡ seg M B

EuclidPropositionI_7short
  |- ∀ A B C D a.
         ¬(A = B) ∧ Line a ∧ A ∈ a ∧ B ∈ a ∧ ¬(C = D) ∧ C ∉ a ∧ D ∉ a ∧
         C,D same_side a  ∧  seg A C ≡ seg A D
         ⇒ ¬(seg B C ≡ seg B D)

EuclidPropositionI_7Help
  |- ∀ A B C D a.
         ¬(A = B) ∧ Line a ∧ A ∈ a ∧ B ∈ a ∧ ¬(C = D) ∧ C ∉ a ∧ D ∉ a ∧ 
         C,D same_side a  ∧  seg A C ≡ seg A D  ∧
         C ∈ int_angle D A B
         ⇒ ¬(seg B C ≡ seg B D)

EuclidPropositionI_7
  |- ∀ A B C D a.
         ¬(A = B) ∧ Line a ∧ A ∈ a ∧ B ∈ a ∧ ¬(C = D) ∧ C ∉ a ∧ D ∉ a ∧ 
         C,D same_side a  ∧  seg A C ≡ seg A D
         ⇒ ¬(seg B C ≡ seg B D)

EuclidPropositionI_11     |- ∀ A B. ¬(A = B)  ⇒  ∃ F. Right (∡ A B F)

DropPerpendicularToLine
  |- ∀ P l.
         Line l  ∧  P ∉ l
         ⇒ ∃ E Q. E ∈ l ∧ Q ∈ l ∧ Right (∡ P Q E)

EuclidPropositionI_14
  |- ∀ A B C D l.
         Line l ∧ A ∈ l ∧ B ∈ l ∧ ¬(A = B) ∧ 
         C ∉ l ∧ D ∉ l  ∧  ¬(C,D same_side l) ∧ 
         ∡ C B A suppl ∡ A B D
         ⇒ B ∈ open (C,D)

VerticalAnglesCong
  |- ∀ A B O A' B'.
         ¬Collinear A O B ∧ O ∈ open (A,A') ∧ O ∈ open (B,B')
         ⇒ ∡ B O A' ≡ ∡ B' O A

EuclidPropositionI_16
  |- ∀ A B C D.
         ¬Collinear A B C  ∧  C ∈ open (B,D)
         ⇒ ∡ B A C <_ang ∡ D C A

ExteriorAngle
  |- ∀ A B C D.
         ¬Collinear A B C  ∧  C ∈ open (B,D)
         ⇒ ∡ A B C <_ang ∡ A C D

EuclidPropositionI_17
  |- ∀ A B C α β γ.
       ¬Collinear A B C  ∧  α = ∡ A B C  ∧  β = ∡ B C A  ∧  β suppl γ
       ⇒ α <_ang γ

EuclidPropositionI_18
  |- ∀ A B C.
         ¬Collinear A B C  ∧  seg A C <__ seg A B
         ⇒ ∡ A B C <_ang ∡ B C A

EuclidPropositionI_19
  |- ∀ A B C.
         ¬Collinear A B C  ∧  ∡ B C A <_ang ∡ A B C
         ⇒ seg A B <__ seg A C

EuclidPropositionI_20
  |- ∀ A B C D.
         ¬Collinear A B C  ∧  A ∈ open (B,D)  ∧  seg A D ≡ seg A C
         ⇒ seg B C <__ seg B D

EuclidPropositionI_21
  |- ∀ A B C D.
         ¬Collinear A B C  ∧  D ∈ int_triangle A B C
         ⇒ ∡ A B C <_ang ∡ C D A

AngleTrichotomy3
  |- ∀ α β γ.
         α <_ang β  ∧  Angle γ  ∧  γ ≡ α
         ⇒ γ <_ang β

CircleConvex
  |- ∀ O A B C.
         ¬Collinear A O C  ∧  B ∈ open (A,C)  ∧  
         seg O A <__ seg O C  ∨  seg O A ≡ seg O C
         ⇒ seg O B <__ seg O C

SegmentTrichotomy3
  |- ∀ s t u. s <__ t  ∧  Segment u  ∧  u ≡ s  ⇒  u <__ t

EuclidPropositionI_24Help
  |- ∀ O A C O' D F.
         ¬Collinear A O C ∧ ¬Collinear D O' F  ∧ 
         seg O' D ≡ seg O A  ∧  seg O' F ≡ seg O C  ∧ 
         ∡ D O' F <_ang ∡ A O C  ∧ 
         seg O A <__ seg O C  ∨  seg O A ≡ seg O C
         ⇒ seg D F <__ seg A C

EuclidPropositionI_24
  |- ∀ O A C O' D F.
         ¬Collinear A O C ∧ ¬Collinear D O' F  ∧ 
         seg O' D ≡ seg O A  ∧  seg O' F ≡ seg O C  ∧ 
         ∡ D O' F <_ang ∡ A O C
         ⇒ seg D F <__ seg A C

EuclidPropositionI_25
  |- ∀ O A C O' D F.
         ¬Collinear A O C ∧ ¬Collinear D O' F  ∧ 
         seg O' D ≡ seg O A  ∧  seg O' F ≡ seg O C  ∧ 
         seg D F <__ seg A C
         ⇒ ∡ D O' F <_ang ∡ A O C

AAS
  |- ∀ A B C A' B' C'.
         ¬Collinear A B C ∧ ¬Collinear A' B' C'  ∧ 
         ∡ A B C ≡ ∡ A' B' C'  ∧  ∡ B C A ≡ ∡ B' C' A'  ∧ 
         seg A B ≡ seg A' B'
         ⇒ A,B,C ≅ A',B',C'

ParallelSymmetry     |- ∀ l k. l ∥ k  ⇒  k ∥ l

AlternateInteriorAngles
  |- ∀ A B C E l m t.
         Line l ∧ A ∈ l ∧ E ∈ l ∧ 
         Line m ∧ B ∈ m ∧ C ∈ m ∧ 
         Line t ∧ A ∈ t ∧ B ∈ t ∧ 
         ¬(A = E) ∧ ¬(B = C) ∧ ¬(A = B) ∧ E ∉ t ∧ C ∉ t ∧ 
         ¬(C,E same_side t)  ∧  ∡ E A B ≡ ∡ C B A
         ⇒ l ∥ m

EuclidPropositionI_28
  |- ∀ A B C D E F G H l m t.
         Line l ∧ A ∈ l ∧ B ∈ l ∧ G ∈ l ∧ 
         Line m ∧ C ∈ m ∧ D ∈ m ∧ H ∈ m ∧ 
         Line t ∧ G ∈ t ∧ H ∈ t ∧ G ∉ m ∧ H ∉ l ∧ 
         G ∈ open (A,B)  ∧  H ∈ open (C,D)  ∧ 
         G ∈ open (E,H)  ∧  H ∈ open (F,G)  ∧  ¬(D,A same_side t)  ∧ 
         ∡ E G B ≡ ∡ G H D  ∨  ∡ B G H suppl ∡ G H D
         ⇒ l ∥ m

OppositeSidesCongImpliesParallelogram
  |- ∀ A B C D.
         Quadrilateral A B C D  ∧ 
         seg A B ≡ seg C D  ∧  seg B C ≡ seg D A
         ⇒ Parallelogram A B C D

P     |- ∀ P l. Line l ∧ P ∉ l ⇒ ∃! m. Line m ∧ P ∈ m ∧ m ∥ l

ConverseAlternateInteriorAngles
  |- ∀ A B C E l m t.
         Line l ∧ A ∈ l ∧ E ∈ l				∧ 
         Line m ∧ B ∈ m ∧ C ∈ m				∧ 
         Line t ∧ A ∈ t ∧ B ∈ t			    	∧ 
         ¬(A = E) ∧ ¬(B = C) ∧ ¬(A = B) ∧ E ∉ t ∧ C ∉ t	∧ 
         ¬(C,E same_side t)  ∧  l ∥ m
         ⇒ ∡ E A B ≡ ∡ C B A

HilbertTriangleSum
  |- ∀ A B C.
         ¬Collinear A B C
         ⇒ ∃ E F.
                  B ∈ open (E,F)  ∧  C ∈ int_angle A B F ∧
                  ∡ E B A ≡ ∡ C A B  ∧  ∡ C B F ≡ ∡ B C A

OppositeAnglesCongImpliesParallelogramHelp
  |- ∀ A B C D a c.
         Quadrilateral A B C D                                ∧ 
         ∡ A B C ≡ ∡ C D A  ∧  ∡ D A B ≡ ∡ B C D             ∧ 
         Line a ∧ A ∈ a ∧ B ∈ a  ∧  Line c ∧ C ∈ c ∧ D ∈ c
         ⇒ a ∥ c

OppositeAnglesCongImpliesParallelogram
  |- ∀ A B C D.
         Quadrilateral A B C D  ∧  
         ∡ A B C ≡ ∡ C D A  ∧  ∡ D A B ≡ ∡ B C D
         ⇒ Parallelogram A B C D

