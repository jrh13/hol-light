(* ========================================================================= *)
(* HOL Light Tarski plane geometry axiomatic proofs up to Gupta's theorem.   *)
(* ========================================================================= *)
(*                                                                           *)
(* This is a port of MML Mizar code published with Adam Grabowski and Jesse  *)
(* Alama, which was a readable version of Julien Narboux's Coq pseudo-code   *)
(* http://dpt-info.u-strasbg.fr/~narboux/tarski.html.  We partially prove a  *)
(* theorem in Schwabhäuser's Ishi Press book Metamathematische Methoden in   *)
(* der Geometrie, that Tarski's plane geometry axioms imply Hilbert's.  We   *)
(* get about as far Gupta's amazing  proof which implies Hilbert's axiom I1  *)
(* that two points determine a line.  	   	 	 	   	     *)
(*                                                                           *)
(* Thanks to Freek Wiedijk, who wrote the HOL Light Mizar interface miz3, in *)
(* which this code was originally written, and John Harrison, who came up    *)
(* with the axiomatic framework here, and recommended writing it in miz3.    *)

needs "RichterHilbertAxiomGeometry/readable.ml";;

new_type("point",0);;

NewConstant("≡",`:point#point->point#point->bool`);;
NewConstant("Between",`:point#point#point->bool`);;

ParseAsInfix("≡",(12, "right"));;
ParseAsInfix("≅",(12, "right"));;
ParseAsInfix("on_line",(12, "right"));;
ParseAsInfix("equal_line",(12, "right"));;

let cong_DEF = NewDefinition
 `;a,b,c ≅ x,y,z ⇔
   a,b ≡ x,y ∧ a,c ≡ x,z ∧ b,c ≡ y,z`;;

let is_ordered_DEF = NewDefinition
 `;is_ordered (a,b,c,d) ⇔
  Between (a,b,c) ∧ Between (a,b,d) ∧ Between (a,c,d) ∧ Between (b,c,d)`;;

let Line_DEF = NewDefinition `;
  x on_line a,b ⇔
  ¬(a = b) ∧ (Between (a,b,x) ∨ Between (a,x,b) ∨ Between (x,a,b))`;;

let  LineEq_DEF = NewDefinition `;
  a,b equal_line x,y ⇔
  ¬(a = b) ∧ ¬(x = y) ∧ ∀ c .  c on_line a,b  ⇔  c on_line x,y`;;

(* ------------------------------------------------------------------------- *)
(* The axioms.                                                               *)
(* ------------------------------------------------------------------------- *)

let A1 = NewAxiom `;
  ∀a b. a,b ≡ b,a`;;

let A2 = NewAxiom `;
  ∀a b p q r s. a,b ≡ p,q ∧ a,b ≡ r,s ⇒ p,q ≡ r,s`;;

let A3 = NewAxiom `;
  ∀a b c. a,b ≡ c,c ⇒ a = b`;;

let A4 = NewAxiom `;
  ∀a q b c. ∃x. Between(q,a,x) ∧ a,x ≡ b,c`;;

let A5 = NewAxiom `;
  ∀a b c x a' b' c' x'.
        ¬(a = b) ∧ a,b,c ≅ a',b',c' ∧
        Between(a,b,x) ∧ Between(a',b',x') ∧ b,x ≡ b',x'
        ⇒ c,x ≡ c',x'`;;

let A6 = NewAxiom `;
  ∀a b. Between(a,b,a) ⇒ a = b`;;

let A7 = NewAxiom `;
  ∀a b p q z.  Between(a,p,z) ∧ Between(b,q,z) 
    ⇒ ∃x. Between(p,x,b) ∧ Between(q,x,a)`;;

(* A4 is the Segment Construction axiom, A5 is the SAS axiom and A7 is
   the Inner Pasch axiom.  There are 4 more axioms we're not using yet:
   there exist 3 non-collinear points;
   3 points equidistant from 2 distinct points are collinear;
   Euclid's ∥ postulate;
   a first order version of Hilbert's Dedekind Cuts axiom.

   We shall say we apply SAS to a+cbx and a'+c'b'x'.  Normally one
   applies SAS by showing cb = c'b' bx = b'x' (which we assume) and
   ∡ cbx ≅ ∡ c'b'x'.  One might prove the ∡ congruence
   by showing that the triangles abc ∧ a'b'c' were congruent by SSS
   (which we also assume) and then apply the theorem that complements
   of congruent angles are congruent.  Hence Tarski's axiom. *)

let EquivReflexive = theorem `;
  ∀a b. a,b ≡ a,b
  by fol A1 A2`;;

let EquivSymmetric = theorem `;
  ∀a b c d. a,b ≡ c,d ⇒ c,d ≡ a,b
  by fol EquivReflexive A2`;;

let EquivTransitive = theorem `;
  ∀a b p q r s.  a,b ≡ p,q ∧ p,q ≡ r,s ⇒ a,b ≡ r,s
  by fol EquivSymmetric A2`;;

let Baaa_THM = theorem `;
  ∀a b. Between (a,a,a) ∧ a,a ≡ b,b
  by fol A4 A3`;;

let Bqaa_THM = theorem `;
  ∀a q. Between(q,a,a)
  by fol A4 A3`;;

let C1_THM = theorem `;
  ∀a b x y. ¬(a = b)  ∧  Between (a,b,x)  ∧  Between (a,b,y)  ∧  b,x ≡ b,y
   ⇒ y = x

  proof
    intro_TAC ∀a b x y, H1 H2 H3 H4;
    a,b,y ≅ a,b,y     [] by fol EquivReflexive cong_DEF;
    y,x ≡ y,y     [] by fol - H1 H2 H3 H4 A5;
    fol - A3;
    qed;
`;;

let Bsymmetry_THM = theorem `;
  ∀a p z.  Between (a,p,z) ⇒ Between (z,p,a)

  proof
    intro_TAC ∀a p z, H1;
    Between (p,z,z)     [] by fol Bqaa_THM;
    consider x such that
    Between (p,x,p) ∧ Between (z,x,a)     [xExists] by fol - H1 A7;
    fol - A6;
  qed;
`;;

let Baaq_THM = theorem `;
  ∀a q.  Between (a,a,q)
  by fol Bqaa_THM Bsymmetry_THM`;;

let BEquality_THM = theorem `;
  ∀a b c.  Between (a,b,c) ∧ Between (b,a,c) ⇒ a = b

  proof
    intro_TAC ∀a b c, H1 H2;
    consider x such that
    Between (b,x,b) ∧ Between (a,x,a)     [A7implies] by fol H2 H1 A7;
    fol - A6;
  qed;
`;;

let B124and234then123_THM = theorem `;
  ∀a b c d. Between (a,b,d)  ∧  Between (b,c,d)  ⇒  Between (a,b,c)

  proof
    intro_TAC ∀a b c d, H1 H2;
    consider x such that
    Between (b,x,b) ∧ Between (c,x,a)     [A7implies] by fol H1 H2 A7;
    fol - A6 Bsymmetry_THM;
  qed;
`;;

let BTransitivity_THM = theorem `;
  ∀a b c d.  ¬(b = c)  ∧  Between (a,b,c)  ∧  Between (b,c,d)
    ⇒  Between (a,c,d)

  proof
    intro_TAC ∀a b c d, H1 H2 H3;
    consider x such that
    Between (a,c,x) ∧ c,x ≡ c,d     [X1] by fol A4;
    Between (x,c,b)     [] by fol H2 Bsymmetry_THM - B124and234then123_THM;
    x = d     [] by fol - Bsymmetry_THM H1 H3 X1 C1_THM;
    fol - X1;
  qed;
`;;

let BTransitivityOrdered_THM = theorem `;
  ∀a b c d.  ¬(b = c)  ∧  Between (a,b,c)  ∧  Between (b,c,d)
    ⇒ is_ordered (a,b,c,d)

  proof
    intro_TAC ∀a b c d, H1 H2 H3;
    Between (a,c,d)     [X1] by fol H1 H2 H3 BTransitivity_THM;
    Between (d,b,a)     [] by fol H2 Bsymmetry_THM H1 H3 BTransitivity_THM;
    fol H2 - Bsymmetry_THM X1 H3 is_ordered_DEF;
  qed;
`;;

let B124and234Ordered_THM = theorem `;
  ∀a b c d.  Between (a,b,d)  ∧  Between (b,c,d)  ⇒  is_ordered (a,b,c,d)

  proof
    intro_TAC ∀a b c d, H1 H2;
    Between (a,b,c)     [Babc] by fol H1 H2 B124and234then123_THM;
    assume ¬(b = c)     [] by fol - Bqaa_THM H1 H2 is_ordered_DEF;
    fol Babc - H2 BTransitivityOrdered_THM;
   qed;
`;;

let SegmentAddition_THM = theorem `;
  ∀a b c a' b' c'.  Between (a,b,c)  ∧ Between (a',b',c')  ∧  
    a,b ≡ a',b'  ∧  b,c ≡ b',c'                                      
    ⇒  a,c ≡ a',c'

  proof
    intro_TAC ∀a b c a' b' c', H1 H2 H3 H4;
    assume ¬(a = b)     [aNOTb] by fol H3 EquivSymmetric A3 H4;
    a,b,a ≅ a',b',a'     [] by fol Baaa_THM H3 A1 EquivTransitive cong_DEF;
    fol - aNOTb H1 H2 H4 A5;
  qed;
`;;

let CongruenceDoubleSymmetry_THM = theorem `;
  ∀a b c d.  a,b ≡ c,d  ⇒  b,a ≡ d,c
  by fol A1 EquivTransitive`;;

let C1prime_THM = theorem `;
  ∀a b x y.  ¬(a = b)  ∧  Between (a,b,x)  ∧  Between (a,b,y)  ∧  a,x ≡ a,y 
    ⇒ x = y

  proof
    intro_TAC ∀a b x y, H1 H2 H3 H4;
    consider m such that
    Between (b,a,m) ∧ a,m ≡ a,b     [X1] by fol A4;
    Between (m,a,b)     [X2] by fol X1 Bsymmetry_THM;
    ¬(m = a)     [X3] by fol X1 EquivSymmetric A3 H1;
    is_ordered (m,a,b,x)     [] by fol H1 X2 H2 BTransitivityOrdered_THM;
    Between (m,a,x)     [X4] by fol - is_ordered_DEF;
    is_ordered (m,a,b,y)     [] by fol H1 X2 H3 BTransitivityOrdered_THM;
    Between (m,a,y)     [] by fol - is_ordered_DEF;
    fol - X3 X4 H4 C1_THM;
    qed;
`;;

let SegmentSubtraction_THM = theorem `;
  ∀a b c a' b' c'.  Between (a,b,c) ∧ Between (a',b',c') ∧ 
    a,b ≡ a',b' ∧ a,c ≡ a',c'  ⇒  b,c ≡ b',c'

  proof
    intro_TAC ∀a b c a' b' c', H1 H2 H3 H4;
    assume ¬(a = b)     [Z1] by fol - H3 EquivSymmetric A3 H4;
    consider x such that
    Between (a,b,x) ∧ b,x ≡ b',c'     [Z2] by fol A4;
    a,x ≡ a',c'     [] by fol - H2 H3 SegmentAddition_THM;
    a,x ≡ a,c     [] by fol H4 EquivSymmetric - EquivTransitive;
    x = c     [] by fol - Z1 Z2 H1 C1prime_THM;
    fol - Z2;
  qed;
`;;

let EasyAngleTransport_THM = theorem `;
    ∀a O b.  ¬(O = a)    
      ⇒ ∃x y.  Between (b,O,x) ∧ Between (a,O,y) ∧ x,y,O ≅ a,b,O

  proof
    intro_TAC ∀a O b, H1;
    consider x y such that
    Between (b,O,x) ∧ O,x ≡ O,a  ∧  
    Between (a,O,y) ∧ O,y ≡ O,b     [X2] by fol A4;
    x,O ≡ a,O     [X3] by fol - CongruenceDoubleSymmetry_THM;
    a,O,x ≅ x,O,a     [X5] by fol - EquivSymmetric A1 X2 cong_DEF;
    x,y ≡ a,b     [] by fol H1 X5 X2 Bsymmetry_THM A5;
    x,y,O ≅ a,b,O     [] by fol - X3 X2 CongruenceDoubleSymmetry_THM cong_DEF;
    fol X2 -;
  qed;
`;;

let B123and134Ordered_THM = theorem `;
  ∀a b c d.  
 Between (a,b,c) ∧ 
 Between (a,c,d) ⇒ 
 is_ordered (a,b,c,d)

  proof
    intro_TAC ∀a b c d, H1 H2;
    is_ordered (d,c,b,a)     [] by fol H2 H1 Bsymmetry_THM B124and234Ordered_THM;
    Between (d,b,a) ∧ Between (d,c,b)     [] by fol - is_ordered_DEF;
    fol - Bsymmetry_THM H1 H2 is_ordered_DEF;
  qed;
`;;

let BextendToLine_THM = theorem `;
  ∀a b c d.  ¬(a = b)  ∧  Between (a,b,c)  ∧  Between (a,b,d) 
    ⇒ ∃x.  is_ordered (a,b,c,x) ∧ is_ordered (a,b,d,x)

  proof
    intro_TAC ∀a b c d, H1 H2 H3;
    consider u such that
    Between (a,c,u) ∧ c,u ≡ b,d     [X1] by fol A4;
    is_ordered (a,b,c,u)     [X2] by fol H2 X1 B123and134Ordered_THM;
    Between (u,c,b)     [X3] by fol X2 is_ordered_DEF Bsymmetry_THM;
    u,c ≡ b,d     [X4] by fol A1 X1 EquivTransitive;
    Between (a,b,u)     [X5] by fol X2 is_ordered_DEF;
    consider x such that
    Between (a,d,x) ∧ d,x ≡ b,c     [Y1] by fol A4;
    is_ordered (a,b,d,x)     [Y2] by fol H3 Y1 B123and134Ordered_THM;
    c,b ≡ d,x     [Y5] by fol A1 Y1 EquivSymmetric EquivTransitive;
    Between (a,b,x)     [Y6] by fol Y2 is_ordered_DEF;
    u,b ≡ b,x     [] by fol X3 Y2 is_ordered_DEF X4 Y5 SegmentAddition_THM;
    u = x     [] by fol A1 - EquivTransitive H1 X5 Y6 C1_THM;
    fol - X2 Y2;
  qed;
`;;

let GuptaEasy_THM = theorem `;
  ∀a b c d.  ¬(a = b) ∧ Between (a,b,c) ∧ Between (a,b,d) ∧  
    ¬(b = c) ∧ ¬(b = d)  ⇒  ¬Between (c,b,d)

  proof
    intro_TAC ∀a b c d, H1 H2 H3 H4 H5;
    assume Between (c,b,d)     [H6] by fol;
    consider x such that
    is_ordered (a,b,c,x) ∧ is_ordered (a,b,d,x)     [X1] by fol H1 H2 H3 BextendToLine_THM;
    Between (b,d,x)     [] by fol X1 is_ordered_DEF;
    is_ordered (c,b,d,x)     [] by fol - H5 H6 BTransitivityOrdered_THM;
    Between (b,c,x) ∧ Between (c,b,x)     [] by fol - X1 is_ordered_DEF;
    fol - BEquality_THM H4;
  qed;
`;;

(* The next result is like SAS: there are 5 pairs of segments 4 equivalent.  *)
(* We apply Inner5Segments to abc-x and a'b'c'-x'.     		     	     *)

let Inner5Segments_THM = theorem `;
  ∀a b c x a' b' c' x'.  a,b,c ≅ a',b',c' ∧ 
    Between (a,x,c) ∧ Between (a',x',c') ∧ c,x ≡ c',x'  ⇒  b,x ≡ b',x'

  proof
    intro_TAC ∀a b c x a' b' c' x', H1 H2 H3 H4;
    a,b ≡ a',b' ∧ a,c ≡ a',c' ∧ b,c ≡ b',c'     [X1] by fol H1 cong_DEF;
    assume ¬(x = c)     [Case2] by fol H4 EquivSymmetric - A3 X1;
    ¬(a = c)     [X2] by fol H2 A6 -;
    consider y such that
    Between (a,c,y) ∧ c,y ≡ a,c     [X3] by fol A4;
    consider y' such that
    Between (a',c',y') ∧ c',y' ≡ a,c     [X4] by fol A4;
    c,y ≡ c',y'     [X5] by fol - X3 EquivSymmetric EquivTransitive;
    c,b ≡ c',b'     [X6] by fol X1 CongruenceDoubleSymmetry_THM;
    a,c,b ≅ a',c',b'     [] by fol cong_DEF X1 -;
    b,y ≡ b',y'     [X7] by fol - X2 X3 X4 X5 A5;
    ¬(y = c)     [X8] by fol X3 EquivSymmetric A3 X2;
    Between (y,c,x)     [X9] by fol X3 H2 Bsymmetry_THM B124and234then123_THM;
    Between (y',c',a') ∧ Between (c',x',a')     [] by fol - X4 H3 Bsymmetry_THM;
    Between (y',c',x')     [X10] by fol - B124and234then123_THM;
    y,c,b ≅ y',c',b'     [] by fol X5 X7 CongruenceDoubleSymmetry_THM cong_DEF X6;
    fol - X8 X9 X10 H4 A5;
  qed;
`;;

let RhombusDiagBisect_THM = theorem `;
  ∀b c d c' d'.  Between (b,c,d') ∧ Between (b,d,c') ∧ 
    c,d' ≡ c,d ∧ d,c' ≡ c,d ∧ d',c' ≡ c,d 
    ⇒ ∃e. Between (c,e,c') ∧ Between (d,e,d') ∧ c,e ≡ c',e ∧ d,e ≡ d',e

  proof
    intro_TAC ∀b c d c' d', H1 H2 H3 H4 H5;
    Between (d',c,b) ∧ Between (c',d,b)     [X1] by fol H1 H2 Bsymmetry_THM;
    consider e such that
    Between (c,e,c') ∧ Between (d,e,d')     [X2] by fol X1 A7;
    c,d ≡ c,d'     [X3] by fol H3 EquivSymmetric;
    c,c' ≡ c,c'     [X4] by fol EquivReflexive;
    c,d,c' ≅ c,d',c'     [] by fol H5 EquivSymmetric H4 EquivTransitive X3 X4 cong_DEF;
    d,e ≡ d',e     [X5] by fol - X2 EquivReflexive Inner5Segments_THM;
    d,c ≡ d,c'     [X7] by fol H4 EquivSymmetric A1 EquivTransitive;
    d,d' ≡ d,d'      [X8] by fol EquivReflexive;
    c,d' ≡ c',d'     [] by fol A1 H5 EquivSymmetric  H3 EquivTransitive;
    d,c,d' ≅ d,c',d'     [] by fol EquivReflexive X7 X8 - cong_DEF;
    c,e ≡ c',e     [] by fol - X2 EquivReflexive Inner5Segments_THM;
    fol - X2 X5;
  qed;
`;;

let FlatNormal_THM = theorem `;
  ∀a b c d d' e.  Between (b,c,d')  ∧  Between (d,e,d')  ∧  
    c,d' ≡ c,d  ∧  d,e ≡ d',e  ∧  ¬(c = d)  ∧  ¬(e = d) 
    ⇒ ∃p r q. Between (p,r,q) ∧ Between (r,c,d') ∧ Between (e,c,p) ∧
    r,c,p ≅ r,c,q ∧ r,c ≡ e,c ∧ p,r ≡ d,e

  proof
    intro_TAC ∀a b c d d' e, H1 H2 H3 H4 H5 H6;
    ¬(c = d')     [] by fol H5 H3 EquivSymmetric A3;
    consider p r such that
    Between (e,c,p) ∧ Between (d',c,r) ∧ p,r,c ≅ d',e,c     [X1] by fol 
    - EasyAngleTransport_THM;
    p,r ≡ d',e ∧ p,c ≡ d',c ∧ r,c ≡ e,c     [X2] by fol - X1 cong_DEF;
    p,r ≡ d,e     [X3] by fol H4 EquivSymmetric X2 EquivTransitive;
    ¬(p = r)     [X4] by fol - EquivSymmetric H6 A3;
    consider q such that
    Between (p,r,q) ∧ r,q ≡ e,d     [X5] by fol A4;
    c,p ≡ c,d     [X7] by fol - X2 CongruenceDoubleSymmetry_THM H3 EquivTransitive;
::  Apply SAS to p+crq /\ d'+ced
    c,q ≡ c,d     [] by fol X4 X1 X5 H2 Bsymmetry_THM A5;
    r,c,p ≅ r,c,q     [] by fol - EquivSymmetric X7 EquivTransitive X5 X3 CongruenceDoubleSymmetry_THM EquivReflexive cong_DEF;
    fol X1 Bsymmetry_THM X5 - X2 X1 X3;
  qed;
`;;

let EqDist2PointsBetween_THM = theorem `;
  ∀a b c p q.  ¬(a = b) ∧ Between (a,b,c) ∧ a,p ≡ a,q ∧ b,p ≡ b,q 
    ⇒ c,p ≡ c,q

  proof
    :: a & b are equidistant from p & q.  Apply SAS to a+pbc /\ a+qbc.
    intro_TAC ∀a b c p q, H1 H2 H3 H4;
    a,b,p ≅ a,b,q     [] by fol EquivReflexive H3 H4 cong_DEF;
    p,c ≡ q,c     [] by fol H1 - H2 EquivReflexive A5;
    fol - CongruenceDoubleSymmetry_THM;
  qed;
`;;

let EqDist2PointsInnerBetween_THM = theorem `;
  ∀a x c p q.  Between (a,x,c)  ∧  a,p ≡ a,q  ∧  c,p ≡ c,q 
    ⇒ x,p ≡ x,q

  proof
    :: a and c are equidistant from p and q.  Apply Inner5Segments to
    :: apb-x /\ aqb-x.
    intro_TAC ∀a x c p q, H1 H2 H3;
    a,p,c ≅ a,q,c     [] by fol H2 H3 CongruenceDoubleSymmetry_THM EquivReflexive cong_DEF;
    p,x ≡ q,x     [] by fol - H1 EquivReflexive Inner5Segments_THM;
    fol - CongruenceDoubleSymmetry_THM;
  qed;
`;;

let Gupta_THM = theorem `;
  ∀a b c d.  ¬(a = b)  ∧  Between (a,b,c)  ∧  Between (a,b,d) 
    ⇒ Between (b,d,c)  ∨  Between (b,c,d)

  proof
    intro_TAC ∀a b c d, H1 H2 H3;
    assume ¬(b = c) ∧ ¬(b = d) ∧ ¬(c = d)     [H4] by fol - Baaq_THM Bqaa_THM;
    assume ¬Between (b,d,c)     [H5] by fol;
    consider d' such that
    Between (a,c,d') ∧ c,d' ≡ c,d     [X1] by fol A4;
    consider c' such that
    Between (a,d,c') ∧ d,c' ≡ c,d     [X2] by fol A4;
    is_ordered (a,b,c,d')     [] by fol H2 X1 B123and134Ordered_THM;
    Between (a,b,d') ∧ Between (b,c,d')     [X3] by fol - is_ordered_DEF;
    is_ordered (a,b,d,c')     [] by fol H3 X2 B123and134Ordered_THM;
    Between (a,b,c') ∧ Between (b,d,c')     [X4] by fol - is_ordered_DEF;
    ¬(c = d')     [X5] by fol X1 H4 A3 EquivSymmetric;
    ¬(d = c')     [X6] by fol X2 H4 A3 EquivSymmetric;
    ¬(b = d')     [X7] by fol X3 H4 A6;
    ¬(b = c')     [X8] by fol X4 H4 A6;

::  In the proof below, we prove a stronger result than
::  BextendToLine_THM with much the same proof.  We find u ∧ b'
::  with essentially a,b,c,d',u and a b,d,c',b' ordered 5-tuples
::  with d'u ≡ db ∧ cb' ≡ bc. 
    consider u such that
    Between (c,d',u) ∧ d',u ≡ b,d     [Y1] by fol A4;
    is_ordered (b,c,d',u)     [] by fol X5 X3 Y1 BTransitivityOrdered_THM;
    Between (b,c,u) ∧  Between (b,d',u)     [Y2] by fol - is_ordered_DEF;
    consider b' such that
    Between (d,c',b') ∧ c',b' ≡ b,c     [Y3] by fol A4;
    is_ordered (b,d,c',b')     [] by fol X6 X4 Y3 BTransitivityOrdered_THM;
    Between (b,d,b') ∧ Between (b,c',b')     [Y4] by fol - is_ordered_DEF;
    c,d' ≡ c',d     [Y7] by fol X2 EquivSymmetric X1 A1 EquivTransitive;
    c,u ≡ c',b     [Y8] by fol Y1 A1 EquivTransitive X4 Bsymmetry_THM Y7 SegmentAddition_THM;
    b,c ≡ b',c'     [Y10] by fol Y3 EquivSymmetric A1 EquivTransitive;
    b,u ≡ b,b'     [Y11] by fol Y4 Bsymmetry_THM Y2 Y10 Y8 SegmentAddition_THM A1 EquivTransitive;
    is_ordered (a,b,d',u)     [Y12] by fol X7 X3 Y2 BTransitivityOrdered_THM;
    is_ordered (a,b,c',b')     [] by fol X8 X4 Y4 BTransitivityOrdered_THM;
    Between (a,b,u) ∧ Between (a,b,b')     [] by fol - Y12 is_ordered_DEF;
    u = b'     [Y13] by fol - H1 Y11 C1_THM;
::  Show c'd' ≡ cd by applying SAS to b+c'cd ∧ b'+cc'd.
    b,c,c' ≅ b',c',c     [Z2] by fol A1 Y10 Y13 Y8 EquivSymmetric CongruenceDoubleSymmetry_THM cong_DEF;
    d',c' ≡ c,d     [] by fol Y3 Bsymmetry_THM H4 Z2 X3 Y7 A5 A1 EquivTransitive;
::  c,d',c',d is a "flat" rhombus.  The diagonals bisect each other.
    consider e such that
    Between (c,e,c') ∧ Between (d,e,d') ∧ c,e ≡ c',e ∧ d,e ≡ d',e     [Z4] by fol - X3 X4 X1 X2 RhombusDiagBisect_THM;
    ¬(e = c)     [U1]
    proof
      assume e = c     [U2] by fol; 
      c' = c     [] by fol U2 Z4 EquivSymmetric A3;
      Between (b,d,c)     [U3] by fol - X4;
      fol - U3 H5;
    qed;
    e = d     [V1]
    proof
      assume ¬(e = d)     [V2] by fol; 
      consider p r q such that
      Between (p,r,q) ∧ Between (r,c,d') ∧ Between (e,c,p) ∧
      r,c,p ≅ r,c,q ∧ r,c ≡ e,c ∧ p,r ≡ d,e     [W1] 
    	proof
    	  MP_TAC ISPECL [a; b; c; d; d'; e] FlatNormal_THM;
    	  fol X3 Z4 X1 H4 V2;
    	qed;
      r,p ≡ r,q ∧ c,p ≡ c,q     [W2] by fol W1 cong_DEF;
::    r and c are equidistant from p and q, r <> c, Between r,c,d', thus also d'
      ¬(c = r)     [] by fol W1 U1 EquivSymmetric A3;
      d',p ≡ d',q     [W3] by fol - W1 W2 EqDist2PointsBetween_THM;
::    c and d' are equidistant from p and q, c <> d', 
::    Between c,d',b', thus also b'.
      b',p ≡ b',q     [W4] by fol Y1 Y13 X5 W2 W3 EqDist2PointsBetween_THM;
::    d' and c are equidistant from p and q, d' <> c, Between d',c,b, thus also b. 
      b,p ≡ b,q     [] by fol X3 Bsymmetry_THM X5 W3 W2 EqDist2PointsBetween_THM;
::    b and b' are equidistant from p and q, Between b,c',b, thus also c'.
      c',p ≡ c',q     [W7] by fol Y4 W4 - EqDist2PointsInnerBetween_THM;
::    c' and c are equidistant from p and q, c' <> c, Between c',c,p, thus also p.
      is_ordered (c',e,c,p)     [] by fol Z4 Bsymmetry_THM U1 W1 BTransitivityOrdered_THM;
      Between (c',c,p)     [W8] by fol - is_ordered_DEF;
      ¬(c' = c)     [] by fol Z4 U1 A6;
      p,p ≡ p,q     [] by fol - W8 W7 W2 EqDist2PointsBetween_THM;
::    Now we deduce a contradiction from p = q.
      fol - W1 A6 EquivSymmetric A3 V2;
    qed;
    fol V1 Z4 EquivSymmetric A3 X3;
  qed;
`;;

(* Using Gupta's theorem, we prove Hilbert's axiom I3; a line is determined  *)
(* by fol two points. 	     	   	     	       	      	 	     *)

let I1part1_THM = theorem `;
  ∀a b x. ¬(a = b)  ∧  ¬(a = x)  ∧  x on_line a,b  ⇒
    ∀c. c on_line a,b   ⇒  c on_line a,x

  proof
    intro_TAC ∀a b x, H1 H2 H3, ∀c, H4;
    Between (a,b,x) ∨ Between (a,x,b) ∨ Between (x,a,b)     [X1] by fol H3 Line_DEF;
    Between (a,b,c) ∨ Between (a,c,b) ∨ Between (c,a,b)     [X2] by fol H4 Line_DEF;
    assume ¬(x = b) ∧ ¬(b = c)     [Case2] by fol - H4 X1 Bsymmetry_THM H2 Line_DEF;
    Between (a,x,c) ∨ Between (a,c,x) ∨ Between (x,a,c)     []
    proof
      case_split Y1 | Y2 | Y3     by fol X1;
      suppose Between (a,b,x);
        case_split Y11 | Bacb | Bcab     by fol X2;
        suppose Between (a,b,c);
          Between (b,x,c) ∨ Between (b,c,x)     [] by fol - Y1 H1 Gupta_THM;
          is_ordered (a,b,x,c) ∨ is_ordered (a,b,c,x)     [] by fol Case2 Y1 Y11 - BTransitivityOrdered_THM;
          fol - is_ordered_DEF;
        end;
        suppose Between (a,c,b);
          is_ordered (a,c,b,x)     [] by fol - Y1 B123and134Ordered_THM;
    	    fol - is_ordered_DEF;
        end;
        suppose Between (c,a,b);
          is_ordered (c,a,b,x)     [] by fol H1 - Y1 BTransitivityOrdered_THM;
    	    fol - is_ordered_DEF Bsymmetry_THM;
    	  end;
      end;
      suppose Between (a,x,b);
        case_split Babc | Y22 | Bcab     by fol X2;
        suppose Between (a,b,c);
          is_ordered (a,x,b,c)     [] by fol - Y2 B123and134Ordered_THM;
    	    fol - is_ordered_DEF;
        end;
        suppose Between (a,c,b);
          consider m such that
          Between (b,a,m) ∧ a,m ≡ a,b     [X5] by fol - A4;
          ¬(a = m)     [X6] by fol H1 X5 EquivSymmetric A3;
          Between (m,a,b)     [] by fol X5 Bsymmetry_THM;   :: m,a,c,b  & m,a,x,b
          Between (m,a,c) ∧ Between (m,a,x)     [] by fol - Y22 Y2 B124and234then123_THM;
          fol - X6 Gupta_THM;
        end;
        suppose Between (c,a,b);
          Between (c,a,x)     [] by fol - Y2 B124and234then123_THM;   :: c,a,x,b
    	    fol - Bsymmetry_THM;
        end;
      end;
      suppose Between (x,a,b);
        case_split Babc | Bacb | Bcab     by fol X2;
        suppose Between (a,b,c);
          is_ordered (x,a,b,c)     [] by fol H1 - Y3 BTransitivityOrdered_THM;
    	    fol - is_ordered_DEF;
          end;
        suppose Between (a,c,b);
    	    fol Y3 - B124and234then123_THM;
        end;  :: x,a,c,b
        suppose Between (c,a,b);
          Between (b,a,x) ∧ Between (b,a,c)     [] by fol Y3 - Bsymmetry_THM;
          fol - H1 Gupta_THM;
        end;
      end;
    qed;
    fol - Bsymmetry_THM H2 Line_DEF;
  qed;
`;;

let I1part2_THM = theorem `;
  ∀a b x.  ¬(a = b) ∧ ¬(a = x) ∧ x on_line a,b  ⇒  a,b equal_line a,x

  proof
    intro_TAC ∀a b x, H1 H2 H3;
    ∀c. c on_line a,b ⇔ c on_line a,x      []
    proof
      intro_TAC ∀c;
      eq_tac     [Left] by fol H1 H2 H3 I1part1_THM;
      b on_line a,x     [] by fol H3 Line_DEF Bsymmetry_THM H2 Line_DEF;
      fol - H1 H2 I1part1_THM;
    qed;
    fol H1 H2 - LineEq_DEF;
  qed;
`;;

let LineEqRefl_THM = theorem `;
  ∀a b.  ¬(a = b)  ⇒  a,b equal_line a,b
  by fol LineEq_DEF`;;

let LineEqA1_THM = theorem `;
  ∀a b.  ¬(a = b)  ⇒  a,b equal_line b,a

  proof
    intro_TAC ∀a b, H1;
    ∀c. c on_line a,b  ⇔  c on_line b,a     [] by fol Line_DEF Bsymmetry_THM H1;
    fol H1 - LineEq_DEF;
  qed;
`;;

let LineEqSymmetric_THM = theorem `;
  ∀a b c d.  ¬(a = b) ∧ ¬(c = d)  ⇒  a,b equal_line c,d 
    ⇒  c,d equal_line a,b
  by fol LineEq_DEF`;;

let LineEqTrans_THM = theorem `;
  ∀a b c d e f.  ¬(a = b) ∧ ¬(c = d) ∧ ¬(e = f)  ⇒  a,b equal_line c,d  ⇒ 
    c,d equal_line e,f ⇒  a,b equal_line e,f

  proof
    intro_TAC ∀a b c d e f, H1, H2, H3;
    ∀y. y on_line a,b  ⇔  y on_line e,f     [] by fol H2 H3 LineEq_DEF;
    fol - H1 LineEq_DEF;
  qed;
`;;

let onlineEq_THM = theorem `;
  ∀a b c d x.  x on_line a,b  ⇒  a,b equal_line c,d 
    ⇒  x on_line c,d
  by fol LineEq_DEF`;;

let I1part2Reverse_THM = theorem `;
  ∀a b y.  ¬(a = b) ∧ ¬(b = y)  ⇒  y on_line a,b  
    ⇒  a,b equal_line y,b

  proof
    intro_TAC ∀a b y, H1, H3;
    a,b equal_line b,a ∧ b,y equal_line y,b     [Y1] by fol H1 LineEqA1_THM;
    y on_line b,a     [] by fol H3 Y1 onlineEq_THM;
    a,b equal_line b,y     [] by fol - H1 Y1 I1part2_THM LineEqTrans_THM;
    fol - H1 Y1 LineEqTrans_THM;
  qed;
`;;

let I1_THM = theorem `;
  ∀a b x y.  ¬(a = b) ∧ ¬(x = y) ∧ a on_line x,y ∧ b on_line x,y 
    ⇒ x,y equal_line a,b

  proof
    intro_TAC ∀a b x y, H1 H2 H3 H4;
    case_split H5 | H6     by fol;
    suppose (x = b);
      b,a equal_line a,b  ∧  x,y equal_line b,y     [] by fol H1 LineEqA1_THM H2 H5 LineEqRefl_THM;
      fol H3 H5 H2 I1part2_THM H1 H2 - LineEqTrans_THM;
    end;
    suppose
      ¬(x = b);
      x,y equal_line x,b     [P4] by fol - H2 H6 H4 I1part2_THM;
      a on_line x,b     [] by fol - H2 H6 H3 onlineEq_THM;
      x,b equal_line a,b     [] by fol - H6 H1 I1part2Reverse_THM;
      fol H1 H2 H6 P4 - LineEqTrans_THM;
    end;
  qed;
`;;
