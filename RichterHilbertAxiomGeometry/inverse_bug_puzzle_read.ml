(* ========================================================================= *)
(*                (c) Copyright, Bill Richter 2013                           *)
(*          Distributed under the same license as HOL Light                  *)
(*                                                                           *)
(* Proof of the Bug Puzzle conjecture of the HOL Light tutorial: Any two     *)
(* triples of points in the plane with the same oriented area can be         *)
(* connected in 5 moves or less (FivemovesOrLess).  Much of the code is      *)
(* due to John Harrison: a proof (NOTENOUGH_4) showing this is the best      *)
(* possible result; an early version of Noncollinear_2Span; the              *)
(* definition of move, which defines a closed subset                         *)
(*       {(A,B,C,A',B',C') | move (A,B,C) (A',B',C')} of R^6 x R^6,          *)
(* i.e. the zero set of a continuous function; FivemovesOrLess_STRONG,       *)
(* which handles the degenerate case (collinear or non-distinct triples),    *)
(* giving a satisfying answer using this "closed" definition of move.        *)
(*                                                                           *)
(* The mathematical proofs are essentially due to Tom Hales.                 *)
(* ========================================================================= *)

needs "Multivariate/determinants.ml";;
needs "RichterHilbertAxiomGeometry/readable.ml";;

new_type_abbrev("triple",`:real^2#real^2#real^2`);;

let VEC2_TAC =
  SIMP_TAC[CART_EQ; LAMBDA_BETA; FORALL_2; SUM_2; DIMINDEX_2; VECTOR_2;
           vector_add; vec; dot; orthogonal; basis;
           vector_neg; vector_sub; vector_mul; ARITH] THEN
  CONV_TAC REAL_RING;;

let oriented_area = new_definition
  `oriented_area (a:real^2,b:real^2,c:real^2) =
  ((b$1 - a$1) * (c$2 - a$2) - (c$1 - a$1) * (b$2 - a$2)) / &2`;;

let move = NewDefinition `;
  ∀A B C A' B' C':real^2. move (A,B,C) (A',B',C') ⇔
  (B = B' ∧ C = C' ∧ collinear {vec 0,C - B,A' - A} ∨
  A = A' ∧ C = C' ∧ collinear {vec 0,C - A,B' - B} ∨
  A = A' ∧ B = B' ∧ collinear {vec 0,B - A,C' - C})`;;

let reachable = NewDefinition `;
  ∀p p'.
  reachable p p'  ⇔  ∃n. ∃s. s 0 = p ∧ s n = p' ∧
  (∀m. 0 <= m ∧ m < n ⇒ move (s m) (s (SUC m)))`;;

let reachableN = NewDefinition `;
  ∀p p'. ∀n.
  reachableN p p' n  ⇔  ∃s. s 0 = p ∧ s n = p' ∧
  (∀m. 0 <= m ∧ m < n ⇒ move (s m) (s (SUC m)))`;;

let move2Cond = NewDefinition `;
  ∀ A B A' B':real^2. move2Cond A B A' B'  ⇔
  ¬collinear {B,A,A'} ∧ ¬collinear {A',B,B'}   ∨
  ¬collinear {A,B,B'} ∧ ¬collinear {B',A,A'}`;;


let oriented_areaSymmetry = theorem `;
  oriented_area (A,B,C) = oriented_area(A',B',C')  ⇒
  oriented_area (B,C,A) = oriented_area (B',C',A')  ∧
  oriented_area (C,A,B) = oriented_area (C',A',B')  ∧
  oriented_area (A,C,B) = oriented_area (A',C',B')  ∧
  oriented_area (B,A,C) = oriented_area (B',A',C')  ∧
  oriented_area (C,B,A) = oriented_area (C',B',A')
  proof
    rewrite oriented_area; VEC2_TAC;
  qed;
`;;

let COLLINEAR_3_2Dzero = theorem `;
  ∀y z:real^2. collinear{vec 0,y,z} ⇔
                  z$1 * y$2 = y$1 * z$2
  proof
    rewrite COLLINEAR_3_2D;     VEC2_TAC;     qed;
`;;

let Noncollinear_3ImpliesDistinct = theorem `;
  ¬collinear {a,b,c}  ⇒  ¬(a = b) ∧ ¬(a = c) ∧ ¬(b = c)
  by fol COLLINEAR_BETWEEN_CASES BETWEEN_REFL`;;

let collinearSymmetry = theorem `;
  collinear {A,B,C}
         ⇒ collinear {A,C,B} ∧ collinear {B,A,C} ∧
             collinear {B,C,A} ∧ collinear {C,A,B} ∧ collinear {C,B,A}
  proof
    {A,C,B} ⊂ {A,B,C} ∧  {B,A,C} ⊂ {A,B,C} ∧
    {B,C,A} ⊂ {A,B,C} ∧  {C,A,B} ⊂ {A,B,C} ∧  {C,B,A} ⊂ {A,B,C}     [] by set;
    fol - COLLINEAR_SUBSET;
  qed;
`;;

let Noncollinear_2Span = theorem `;
  ∀u v w:real^2. ¬collinear  {vec 0,v,w} ⇒ ∃ s t. s % v + t % w = u

  proof
    intro_TAC ∀u v w, H1;
    ¬(v$1 * w$2 - w$1 * v$2 = &0)     [H1'] by fol H1 COLLINEAR_3_2Dzero REAL_SUB_0;
    consider M such that
    M = transp(vector[v;w]):real^2^2     [Mexists] by fol -;
    ¬(det M = &0) ∧
    (∀ x. (M ** x)$1 = v$1 * x$1 + w$1 * x$2  ∧
    (M ** x)$2 = v$2 * x$1 + w$2 * x$2)     [MatMult] by simplify H1' Mexists matrix_vector_mul DIMINDEX_2 SUM_2
    TRANSP_COMPONENT VECTOR_2 LAMBDA_BETA ARITH CART_EQ FORALL_2 DET_2;
    ∀ r n. ¬(r < n)  ∧  r <= MIN n n  ⇒  r = n     [] by arithmetic;
    consider x such that M ** x = u     [xDef] by fol MatMult - DET_EQ_0_RANK RANK_BOUND MATRIX_FULL_LINEAR_EQUATIONS;
    exists_TAC x$1;
    exists_TAC x$2;
    x$1 * v$1 + x$2 * w$1 = u$1  ∧
    x$1 * v$2 + x$2 * w$2 = u$2     [xDef] by fol MatMult xDef REAL_MUL_SYM;
    simplify - CART_EQ LAMBDA_BETA FORALL_2 SUM_2 DIMINDEX_2 VECTOR_2 vector_add vector_mul ARITH;
  qed;
`;;

let moveInvariant = theorem `;
  ∀p p'. move p p' ⇒ oriented_area p = oriented_area p'
  proof
    rewrite FORALL_PAIR_THM move oriented_area COLLINEAR_LEMMA  vector_mul; VEC2_TAC;
  qed;
`;;

let ReachLemma = theorem `;
  ∀p p'. reachable p p'  ⇔  ∃n.  reachableN p p' n
  proof
    rewrite reachable reachableN;
  qed;
`;;

let reachableN_CLAUSES = theorem `;
  ∀ p p'. (reachableN p p' 0  ⇔  p = p') ∧
  ∀ n. reachableN p p' (SUC n)  ⇔  ∃ q. reachableN p q n  ∧ move q p'

  proof
    intro_TAC ∀p p';
    consider s0 such that s0 =  λm:num. p:triple     [s0exists] by fol;
    reachableN p p' 0  ⇔  p = p'     [0CLAUSE] by fol s0exists LE_0 reachableN LT;
    ∀ n. reachableN p p' (SUC n)  ⇒  ∃ q. reachableN p q n  ∧ move q p'     [Imp1]
    proof
      intro_TAC ∀n, H1;
      consider s such that
      s 0 = p ∧ s (SUC n) = p' ∧ ∀m. m < SUC n ⇒ move (s m) (s (SUC m))     [sDef] by fol H1 LE_0 reachableN;
      consider q such that q = s n     [qDef] by fol;
      fol sDef qDef LE_0 reachableN LT;
    qed;
    ∀n. (∃ q. reachableN p q n  ∧ move q p')  ⇒  reachableN p p' (SUC n)     [Imp2]
    proof
      intro_TAC ∀n;
      rewrite IMP_CONJ LEFT_IMP_EXISTS_THM;
      intro_TAC ∀q, nReach, move_qp';
      consider s such that
      s 0 = p ∧ s n = q ∧ ∀m. m < n ⇒ move (s m) (s (SUC m))     [sDef] by fol nReach reachableN LT LE_0;
      rewrite reachableN LT LE_0;
      exists_TAC λm. if m < SUC n then s m else p';
      fol sDef move_qp' LT_0 LT_REFL LT LT_SUC;
    qed;
    fol 0CLAUSE Imp1 Imp2;
  qed;
`;;

let reachableInvariant = theorem `;
  ∀p p'. reachable p p'  ⇒  oriented_area p = oriented_area p'

  proof
    simplify ReachLemma LEFT_IMP_EXISTS_THM SWAP_FORALL_THM;
    MATCH_MP_TAC num_INDUCTION;
    simplify reachableN_CLAUSES;
    intro_TAC ∀n, nStep;
    fol nStep moveInvariant;
  qed;
`;;

let reachableN_One = theorem `;
  reachableN P0 P1 1 ⇔ move P0 P1
  by fol ONE reachableN reachableN_CLAUSES`;;

let reachableN_Two = theorem `;
  reachableN P0 P2 2 ⇔ ∃P1. move P0 P1 ∧ move P1 P2
  by fol TWO reachableN_One reachableN_CLAUSES`;;

let reachableN_Three = theorem `;
  reachableN P0 P3 3  ⇔  ∃P1 P2. move P0 P1 ∧ move P1 P2 ∧ move P2 P3
  by fol ARITH_RULE [3 = SUC 2] reachableN_Two reachableN_CLAUSES`;;

let reachableN_Four = theorem `;
  reachableN P0 P4 4  ⇔  ∃P1 P2 P3. move P0 P1 ∧ move P1 P2 ∧
  move P2 P3 ∧ move P3 P4
  by fol ARITH_RULE [4 = SUC 3] reachableN_Three reachableN_CLAUSES`;;

let reachableN_Five = theorem `;
  reachableN P0 P5 5  ⇔  ∃P1 P2 P3 P4. move P0 P1 ∧ move P1 P2 ∧
  move P2 P3 ∧ move P3 P4 ∧ move P4 P5
  proof
    rewrite ARITH_RULE [5 = SUC 4] reachableN_CLAUSES;
    fol reachableN_Four;
  qed;
`;;

let moveSymmetry = theorem `;
  move (A,B,C) (A',B',C') ⇒
  move (B,C,A) (B',C',A') ∧ move (C,A,B) (C',A',B') ∧
  move (A,C,B) (A',C',B') ∧ move (B,A,C) (B',A',C') ∧ move (C,B,A) (C',B',A')

  proof
    ∀X Y Z X':real^2. collinear {vec 0, Z - Y, X' - X}
    ⇒ collinear {vec 0, Y - Z, X' - X}     []
    proof     rewrite COLLINEAR_3_2Dzero;     VEC2_TAC;     qed;
    MP_TAC -;
    rewrite move;
    ∀X Y Z X':real^2. collinear {vec 0, Z - Y, X' - X}
      ⇒ collinear {vec 0, Y - Z, X' - X}     []
    proof     rewrite COLLINEAR_3_2Dzero;     VEC2_TAC;     qed;
    MP_TAC -;
    rewrite move;
    fol;
  qed;
`;;

let reachableNSymmetry = theorem `;
  ∀ n. ∀ A B C A' B' C'. reachableN (A,B,C) (A',B',C') n  ⇒
  reachableN (B,C,A) (B',C',A') n  ∧  reachableN (C,A,B) (C',A',B') n ∧
  reachableN (A,C,B) (A',C',B') n  ∧  reachableN (B,A,C) (B',A',C') n ∧
  reachableN (C,B,A) (C',B',A') n

  proof
    MATCH_MP_TAC num_INDUCTION;
    rewrite reachableN_CLAUSES; simplify PAIR_EQ;
    intro_TAC ∀n, nStep, ∀A B C A' B' C';
    rewrite LEFT_IMP_EXISTS_THM FORALL_PAIR_THM;
    intro_TAC ∀[X] [Y] [Z], XYZexists;
    rewrite RIGHT_AND_EXISTS_THM LEFT_AND_EXISTS_THM;
    exists_TAC (Y,Z,X);
    exists_TAC (Z,X,Y);
    exists_TAC (X,Z,Y);
    exists_TAC (Y,X,Z);
    exists_TAC (Z,Y,X);
    simplify nStep XYZexists moveSymmetry;
  qed;
`;;

let ORIENTED_AREA_COLLINEAR_CONG = theorem `;
  ∀ A B C A' B' C.
    oriented_area (A,B,C) = oriented_area (A',B',C')
    ⇒ (collinear {A,B,C} ⇔ collinear {A',B',C'})
  proof
    rewrite COLLINEAR_3_2D oriented_area; real_ring;
  qed;
`;;

let Basic2move_THM = theorem `;
 ∀ A B C A'. ¬collinear {A,B,C} ∧ ¬collinear {B,A,A'} ⇒
   ∃X. move (A,B,C) (A,B,X)  ∧  move (A,B,X) (A',B,X)

  proof
    intro_TAC ∀A B C A', H1 H2;
    ∀r. r % (A - B) = (--r) % (B - A)  ∧
      r % (A - B) = r % (A - B) + &0 % (C - B)     [add0vector_mul] by VEC2_TAC;
    ¬ ∃ r. A' - A = r % (A - B)     [H2'] by fol - H2 COLLINEAR_3 COLLINEAR_LEMMA;
    consider r t such that A' - A = r % (A - B) + t % (C - B)     [rExists] by fol - H1 COLLINEAR_3 Noncollinear_2Span;
    ¬(t = &0)     [tNonzero] by fol - add0vector_mul H2';
    consider s X such that s = r / t  ∧  X = C + s % (A - B)     [Xexists] by fol rExists;
    A' - A = (t * s) % (A - B) + t % (C - B)     [] by fol - rExists tNonzero REAL_DIV_LMUL;
    A' - A = t % (X - B) ∧ X - C = (-- s) % (B - A)     []
    proof     rewrite - Xexists;     VEC2_TAC;     qed;
    collinear {vec 0,B - A,X - C}  ∧  collinear {vec 0,X - B,A' - A}     [] by fol - COLLINEAR_LEMMA;
    fol - move;
  qed;
`;;

let FourStepMoveAB = theorem `;
  ∀A B C A' B'. ¬collinear {A,B,C} ⇒
  ¬collinear {B,A,A'} ∧ ¬collinear {A',B,B'} ⇒
  ∃ X Y. move (A,B,C) (A,B,X)  ∧  move (A,B,X) (A',B,X)  ∧
  move (A',B,X) (A',B,Y)  ∧  move (A',B,Y) (A',B',Y)

  proof
    intro_TAC ∀A B C A' B', H1, H2;
    consider X such that
    move (A,B,C) (A,B,X)  ∧  move (A,B,X) (A',B,X)     [ABX] by fol H1 H2 Basic2move_THM;
   ¬collinear {A,B,X} ∧ ¬collinear {A',B,X}     [] by fol - H1 moveInvariant ORIENTED_AREA_COLLINEAR_CONG;
   ¬collinear {B,A',X}     [] by fol -  collinearSymmetry;
    consider Y such that
    move (B,A',X) (B,A',Y)  ∧  move (B,A',Y) (B',A',Y)     [BA'Y] by fol - H2 Basic2move_THM;
    move (A',B,X) (A',B,Y)  ∧  move (A',B,Y) (A',B',Y)     [] by fol - BA'Y moveSymmetry;
    fol - ABX;
  qed;
`;;

let FourStepMoveABBAreach = theorem `;
  ∀A B C A' B'. ¬collinear {A,B,C} ∧ move2Cond A B A' B' ⇒
  ∃ Y. reachableN (A,B,C) (A',B',Y) 4

  proof
    intro_TAC ∀A B C A' B', H1 H2;
    case_split Case1 | Case2     by fol - H2 move2Cond;
    suppose ¬collinear {B,A,A'} ∧ ¬collinear {A',B,B'};
      fol - H1 FourStepMoveAB reachableN_Four;
    end;
    suppose ¬collinear {A,B,B'} ∧ ¬collinear {B',A,A'};
      ¬collinear {B,A,C}     [] by fol H1 collinearSymmetry;
      consider X Y such that
      move (B,A,C) (B,A,X)  ∧  move (B,A,X) (B',A,X) ∧
      move (B',A,X) (B',A,Y)  ∧  move (B',A,Y) (B',A',Y)     [BAX] by fol Case2 - FourStepMoveAB;
      fol - moveSymmetry reachableN_Four;
    end;
  qed;
`;;

let NotMove2ImpliesCollinear = theorem `;
  ∀A B C A' B' C'. ¬collinear {A,B,C} ∧ ¬collinear {A',B',C'} ∧
  ¬(A = A') ∧ ¬(B = B') ∧ ¬move2Cond A B A' B' ⇒
  collinear {A,B,A',B'}

  proof
    intro_TAC ∀A B C A' B' C', H1 H1' H2 H2' H3;
    ¬(A = B) ∧ ¬(A' = B')     [Distinct] by fol H1 H1' Noncollinear_3ImpliesDistinct;
    {A,B,A',B'} ⊂ {A,A',B,B'}  ∧
    {A,B,A',B'} ⊂ {B,B',A',A}  ∧  {A,B,A',B'} ⊂ {A',B',B,A}     [set4symmetry] by  SET_TAC;
    case_split Case1 | Case2 | Case3 | Case4     by fol H3 move2Cond;
    suppose collinear {B,A,A'} ∧ collinear {A,B,B'};
      fol - Distinct H2 H2' set4symmetry collinearSymmetry COLLINEAR_4_3 COLLINEAR_SUBSET;
    end;
    suppose collinear {B,A,A'} ∧ collinear {B',A,A'};
      fol - Distinct H2 H2' set4symmetry collinearSymmetry COLLINEAR_4_3 COLLINEAR_SUBSET;
    end;
    suppose collinear {A',B,B'} ∧ collinear {A,B,B'};
      fol - Distinct H2 H2' set4symmetry collinearSymmetry COLLINEAR_4_3 COLLINEAR_SUBSET;
    end;
    suppose collinear {A',B,B'} ∧ collinear {B',A,A'};
      fol - Distinct H2 H2' set4symmetry collinearSymmetry COLLINEAR_4_3 COLLINEAR_SUBSET;
    end;
  qed;
`;;

let NotMove2ImpliesCollinear = theorem `;
  ∀A B C A' B' C'. ¬collinear {A,B,C} ∧ ¬collinear {A',B',C'} ∧
  ¬(A = A') ∧ ¬(B = B') ∧ ¬move2Cond A B A' B' ⇒
  collinear {A,B,A',B'}

  proof
    intro_TAC ∀A B C A' B' C', H1 H1' H2 H2' H3;
    ¬(A = B) ∧ ¬(A' = B')     [Distinct] by fol H1 H1' Noncollinear_3ImpliesDistinct;
    {A,B,A',B'} ⊂ {A,A',B,B'}  ∧
    {A,B,A',B'} ⊂ {B,B',A',A}  ∧  {A,B,A',B'} ⊂ {A',B',B,A}     [set4symmetry] by  SET_TAC;
    collinear {B,A,A'} ∧ collinear {A,B,B'}  ∨
    collinear {B,A,A'} ∧ collinear {B',A,A'}  ∨
    collinear {A',B,B'} ∧ collinear {A,B,B'}  ∨
    collinear {A',B,B'} ∧ collinear {B',A,A'} [] by fol H3 move2Cond;
    fol - Distinct H2 H2' set4symmetry collinearSymmetry COLLINEAR_4_3 COLLINEAR_SUBSET;
  qed;
`;;

let DistinctImplies2moveable = theorem `;
  ∀A B C A' B' C'. ¬collinear {A,B,C} ∧ ¬collinear {A',B',C'} ∧
  ¬(A = A') ∧ ¬(B = B') ∧ ¬(C = C')  ⇒
  move2Cond A B A' B' ∨ move2Cond B C B' C'

  proof
    intro_TAC ∀A B C A' B' C', H1 H1' H2a H2b H2c;
    {A,B,B'} ⊂ {A,B,A',B'} ∧ {B,B',C} ⊂ {B,C,B',C'}     [3subset4] by SET_TAC;
    assume ¬move2Cond A B A' B'  ∧ ¬move2Cond B C B' C'     [Con] by fol;
    collinear {A,B,A',B'} ∧ collinear {B,C,B',C'}     [] by fol - H1 H1' H2a H2b H2c collinearSymmetry NotMove2ImpliesCollinear;
    collinear {A,B,C}     [] by fol - 3subset4 H2a H2b H2c COLLINEAR_SUBSET COLLINEAR_3_TRANS;
    fol - H1 H1';
  qed;
`;;

let SameCdiffAB = theorem `;
  ∀A B C A' B' C'.  ¬collinear {A,B,C} ∧ ¬collinear {A',B',C'} ⇒
  C = C' ∧ ¬(A = A') ∧ ¬(B = B') ⇒
  ∃ Y. reachableN (A,B,C) (Y,B',C') 2  ∨ reachableN (A,B,C) (A',B',Y) 4

  proof
    intro_TAC ∀A B C A' B' C', H1, H2;
    {B,B',A} ⊂ {A,B,A',B'}  ∧  {A,B,C} ⊂ {B,B',A,C}     [easy_set] by SET_TAC;
    case_split Ncol | move | col_Nmove     by fol;
    suppose ¬collinear {C,B,B'};
      consider X such that move (B,C,A) (B,C,X) ∧ move (B,C,X) (B',C',X)     [BCX] by fol - easy_set H1 H2 collinearSymmetry Basic2move_THM;
      fol BCX reachableN_Two reachableNSymmetry;
    end;
    suppose move2Cond A B A' B';
      fol - H1 FourStepMoveABBAreach;
    end;
    suppose collinear {C,B,B'}  ∧  ¬move2Cond A B A' B';
      collinear {B,B',A} ∧ collinear {B,B',C}     [] by fol - H1 H2 easy_set NotMove2ImpliesCollinear COLLINEAR_SUBSET collinearSymmetry;
      fol - H2 easy_set H1 COLLINEAR_4_3 COLLINEAR_SUBSET;
    end;
  qed;
`;;

let FourMovesToCorrectTwo = theorem `;
  ∀A B C A' B' C'. ¬collinear {A,B,C} ∧ ¬collinear {A',B',C'} ⇒
  ∃ n. n < 5 ∧ ∃ Y. reachableN (A,B,C) (A',B',Y) n  ∨
    reachableN (A,B,C) (A',Y,C') n  ∨ reachableN (A,B,C) (Y,B',C') n

  proof
    intro_TAC ∀A B C A' B' C', H1;
    ¬collinear {B,C,A} ∧
    ¬collinear{B',C',A'} ∧ ¬collinear {C,A,B} ∧ ¬collinear {C',A',B'}     [H1'] by fol H1 collinearSymmetry;
    0 < 5 ∧ 2 < 5 ∧ 3 < 5 ∧ 4 < 5     [easy_arith] by ARITH_TAC;
    case_split case01 | case2 | case3     by fol;
    suppose A = A' ∧ B = B' ∧ C = C'  ∨
    A = A' ∧ B = B' ∧ ¬(C = C')  ∨  A = A' ∧ ¬(B = B') ∧ C = C' ∨
    ¬(A = A') ∧ B = B' ∧ C = C';
      fol - easy_arith reachableN_CLAUSES;
    end;
    suppose A = A' ∧ ¬(B = B') ∧ ¬(C = C')  ∨
    ¬(A = A') ∧ B = B' ∧ ¬(C = C')  ∨  ¬(A = A') ∧ ¬(B = B') ∧ C = C';
      fol - H1 H1' easy_arith SameCdiffAB reachableNSymmetry;
    end;
    suppose ¬(A = A') ∧ ¬(B = B') ∧ ¬(C = C');
      exists_TAC 4;
      simplify easy_arith reachableN_CLAUSES;
      fol - H1  H1' DistinctImplies2moveable FourStepMoveABBAreach
    reachableNSymmetry reachableN_Four;
    end;
  qed;
`;;

let CorrectFinalPoint = theorem `;
 oriented_area (A,B,C) = oriented_area (A,B,C') ⇒
   move (A,B,C) (A,B,C')
  proof
    rewrite move oriented_area COLLINEAR_3_2Dzero; VEC2_TAC;
  qed;
`;;

let FiveMovesOrLess = theorem `;
 ∀A B C A' B' C'. ¬collinear {A,B,C}  ∧
  oriented_area (A,B,C) = oriented_area (A',B',C') ⇒
   ∃ n. n <= 5 ∧ reachableN (A,B,C) (A',B',C') n

  proof
    intro_TAC ∀A B C A' B' C', H1 H2;
    ¬collinear {A',B',C'}     [H1'] by fol H1 H2 ORIENTED_AREA_COLLINEAR_CONG;
    ¬(A = B) ∧ ¬(A = C) ∧ ¬(B = C) ∧
    ¬(A' = B') ∧ ¬(A' = C') ∧ ¬(B' = C')     [Distinct] by fol - H1 Noncollinear_3ImpliesDistinct;
    consider n Y such that
    n < 5 ∧ (reachableN (A,B,C) (A',B',Y) n ∨
    reachableN (A,B,C) (A',Y,C') n ∨ reachableN (A,B,C) (Y,B',C') n)     [2Correct] by fol H1 H1' FourMovesToCorrectTwo;
    case_split A'B'Y | A'YC' | YB'C'     by fol 2Correct;
    suppose reachableN (A,B,C) (A',B',Y) n;
      oriented_area (A',B',Y) = oriented_area (A',B',C')     [] by fol - H2 ReachLemma reachableInvariant;
      move (A',B',Y) (A',B',C')     [] by fol - Distinct CorrectFinalPoint;
      fol A'B'Y - 2Correct reachableN_CLAUSES LE_SUC_LT;
    end;
    suppose reachableN (A,B,C) (A',Y,C') n;
      oriented_area (A',C',Y) = oriented_area (A',C',B')     [] by fol H2 - ReachLemma reachableInvariant oriented_areaSymmetry;
      move (A',Y,C') (A',B',C')     [] by fol - Distinct CorrectFinalPoint moveSymmetry;
      fol A'YC' - 2Correct reachableN_CLAUSES LE_SUC_LT;
    end;
    suppose reachableN (A,B,C) (Y,B',C') n;
      oriented_area (B',C',Y) = oriented_area (B',C',A')     [] by fol H2 - ReachLemma reachableInvariant oriented_areaSymmetry;
      move (Y,B',C') (A',B',C')     [] by fol - Distinct CorrectFinalPoint moveSymmetry;
      fol YB'C' - 2Correct reachableN_CLAUSES LE_SUC_LT;
    end;
  qed;
`;;

let NOTENOUGH_4 = theorem `;
  ∃p0 p4. oriented_area p0 = oriented_area p4 ∧ ¬reachableN p0 p4 4

  proof
    consider p0 p4 such that
    p0:triple = vector [&0;&0],vector [&0;&1],vector [&1;&0]  ∧
    p4:triple = vector [&1;&1],vector [&1;&2],vector [&2;&1]     [p04Def] by
    fol;
    oriented_area p0 = oriented_area p4     [equal_areas]
    proof     rewrite - oriented_area;     VEC2_TAC;     qed;
    ¬reachableN p0 p4 4     []
    proof
      rewrite p04Def reachableN_Four NOT_EXISTS_THM FORALL_PAIR_THM move COLLINEAR_3_2Dzero FORALL_VECTOR_2;
      VEC2_TAC;
    qed;
    fol - equal_areas;
  qed;
`;;

let FiveMovesOrLess_STRONG = theorem `;
  ∀A B C A' B' C'.
    oriented_area (A,B,C) = oriented_area (A',B',C') ⇒
    ∃n. n <= 5 ∧ reachableN (A,B,C) (A',B',C') n

  proof
    intro_TAC ∀A B C A' B' C', H1;
    (∀X Y:real^2. collinear {X,Y,Y}) ∧
    (∀A B A'. move (A,B,B) (A',B,B))  ∧
    ∀A B C B'. (collinear {A,B,C} ∧ collinear {A,B',C}  ⇒
    move (A,B,C) (A,B',C))     [EZcollinear]
    proof     rewrite move COLLINEAR_3_2D;     VEC2_TAC;     qed;
    case_split ABCncol | ABCcol     by fol ;
    suppose ¬collinear {A,B,C};
      fol - H1 FiveMovesOrLess;
    end;
    suppose collinear {A,B,C};
      collinear {A',B',C'}     [A'B'C'col] by fol - H1 ORIENTED_AREA_COLLINEAR_CONG;
      consider P1 P2 P3 P4 such that
      P1 = A,C,C  ∧  P2 = B',C,C  ∧  P3 = B',B',C  ∧  P4 = B',B',C'     [P1234exist] by fol;
      move (A,B,C) P1  ∧  move P1 P2  ∧  move P2 P3  ∧  move P3 P4  ∧
      move P4 (A',B',C')     [] by fol ABCcol A'B'C'col EZcollinear P1234exist
      collinearSymmetry moveSymmetry;
      fol -  reachableN_Five LE_REFL;
    end;
  qed;
`;;

