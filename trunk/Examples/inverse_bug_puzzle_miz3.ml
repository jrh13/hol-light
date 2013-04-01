(* ========================================================================= *)
(*                (c) Copyright, Bill Richter 2013                           *)
(*          Distributed under the same license as HOL Light                  *)
(*                                                                           *)
(*  Proof of the Bug Puzzle conjecture of the HOL Light tutorial:            *)
(*  Any two triples with the same oriented area can be connected in          *)
(*  5 moves or less (FiveMovesOrLess).  Also a proof that 4 moves is not     *)
(*  enough, with an explicit counterexample.  This result (NOTENOUGH_4)      *)
(*  is due to John Harrison, as is much of the basic vector code, and        *)
(*  the definition of move, which defines a closed subset                    *)
(*    {(A,B,C,A',B',C') | move (A,B,C) (A',B',C')}  subset  R^6 x R^6        *)
(*  and also a result FiveMovesOrLess_STRONG that handles the degenerate     *)
(*  case (the two triples not required to be non-collinear), which has a     *)
(*  very satisfying answer using this "closed" definition of move.           *)
(*                                                                           *)
(*  The mathematical proofs are essentially due to Tom Hales.  The           *)
(*  code is all in miz3, and was an attempt to explore Freek Wiedijk's       *)
(*  vision of mixing the procedural and declarative proof styles.            *)
(* ========================================================================= *)

needs "Multivariate/determinants.ml";;
 
#load "unix.cma";;
loadt "miz3/miz3.ml";;

new_type_abbrev("triple",`:real^2#real^2#real^2`);;

default_prover := ("ya prover",
    fun thl -> REWRITE_TAC thl THEN CONV_TAC (HOL_BY thl));;

horizon := 0;;
timeout := 500;;

let VEC2_TAC =
  SIMP_TAC[CART_EQ; LAMBDA_BETA; FORALL_2; SUM_2; DIMINDEX_2; VECTOR_2;
           vector_add; vec; dot; orthogonal; basis;
           vector_neg; vector_sub; vector_mul; ARITH] THEN
  CONV_TAC REAL_RING;;

let COLLINEAR_3_2Dzero = thm `;
  !y z:real^2. collinear{vec 0,y,z} <=>
                  z$1 * y$2 = y$1 * z$2
  by REWRITE_TAC[COLLINEAR_3_2D] THEN VEC2_TAC;
`;;

let Noncollinear_3ImpliesDistinct = thm `;
  !a b c:real^N. ~collinear {a,b,c}  ==>  ~(a = b) /\ ~(a = c) /\ ~(b = c)
  by COLLINEAR_BETWEEN_CASES, BETWEEN_REFL;
`;;

let collinearSymmetry = thm `;
  let A B C be real^N;
  thus collinear {A,B,C}  ==>  collinear {A,C,B} /\ collinear {B,A,C} /\
  collinear {B,C,A} /\ collinear {C,A,B} /\ collinear {C,B,A}

  proof
    {A,C,B} SUBSET {A,B,C}  /\  {B,A,C} SUBSET {A,B,C}  /\  {B,C,A} SUBSET {A,B,C}  /\
    {C,A,B} SUBSET {A,B,C}  /\  {C,B,A} SUBSET {A,B,C}     by SET_RULE;
  qed     by -, COLLINEAR_SUBSET;
`;;

let Noncollinear_2Span = thm `;
  let u v w be real^2;
  assume ~collinear  {vec 0,v,w}        [H1];
  thus ? s t. s % v + t % w = u

  proof
    !n r. ~(r < n)  /\  r <= MIN n n  ==>  r = n     [easy_arith] by ARITH_RULE;
    ~(w$1 * v$2 = v$1 * w$2)     [H1'] by H1, COLLINEAR_3_2Dzero;
    consider M such that
    M = transp(vector[v;w]):real^2^2     [Mexists];
    det M = v$1 * w$2 - w$1 * v$2     by -, DIMINDEX_2, SUM_2, TRANSP_COMPONENT, VECTOR_2, LAMBDA_BETA, ARITH, CART_EQ, FORALL_2, DET_2;
    ~(det M = &0)     by -, H1', REAL_ARITH;
    consider x s t such that
    M ** x = u /\ s = x$1 /\ t = x$2     by -, easy_arith, DET_EQ_0_RANK, RANK_BOUND, MATRIX_FULL_LINEAR_EQUATIONS;
     v$1 * s + w$1 * t = u$1  /\  v$2 * s + w$2 * t = u$2     by Mexists, -, SIMP_TAC[matrix_vector_mul; DIMINDEX_2; SUM_2; TRANSP_COMPONENT; VECTOR_2; LAMBDA_BETA; ARITH; CART_EQ; FORALL_2] THEN MESON_TAC[];
    s % v + t % w = u     by -, REAL_MUL_SYM, VECTOR_MUL_COMPONENT, VECTOR_ADD_COMPONENT, VEC2_TAC;
  qed     by -;
`;;

let oriented_area = new_definition
  `oriented_area (a:real^2,b:real^2,c:real^2) =
  ((b$1 - a$1) * (c$2 - a$2) - (c$1 - a$1) * (b$2 - a$2)) / &2`;;

let oriented_areaSymmetry = thm `;
  !A B C A' B' C':real^2.
  oriented_area (A,B,C) = oriented_area(A',B',C')  ==>
  oriented_area (B,C,A) = oriented_area (B',C',A')  /\
  oriented_area (C,A,B) = oriented_area (C',A',B')  /\
  oriented_area (A,C,B) = oriented_area (A',C',B')  /\
  oriented_area (B,A,C) = oriented_area (B',A',C')  /\
  oriented_area (C,B,A) = oriented_area (C',B',A')
  by     REWRITE_TAC[oriented_area] THEN VEC2_TAC;
`;;

let move = new_definition
  `!A B C A' B' C':real^2. move (A,B,C) (A',B',C') <=>
  (B = B' /\ C = C' /\ collinear {vec 0,C - B,A' - A} \/
  A = A' /\ C = C' /\ collinear {vec 0,C - A,B' - B} \/
  A = A' /\ B = B' /\ collinear {vec 0,B - A,C' - C})`;;

let moveInvariant = thm `;
  let p p' be triple;
  assume move p p'                                              [H1];
  thus oriented_area p = oriented_area p'

  proof
    consider X Y Z X' Y' Z' such that
    p = X,Y,Z /\ p' = X',Y',Z'     [pDef] by PAIR_SURJECTIVE;
    move (X,Y,Z) (X',Y',Z')     by -, H1;
    oriented_area (X,Y,Z) = oriented_area (X',Y',Z')     by -, SIMP_TAC[move; oriented_area; COLLINEAR_3; COLLINEAR_3_2Dzero] THEN VEC2_TAC;
  qed     by -, pDef;
`;;

let reachable = new_definition
  `!p p'.
  reachable p p' <=> ?n. ?s.
  s 0 = p /\ s n = p' /\
  (!m. 0 <= m /\ m < n ==> move (s m) (s (SUC m)))`;;

let reachableN = new_definition
  `!p p'. !n.
  reachableN p p' n <=> ?s.
  s 0 = p /\ s n = p' /\
  (!m. 0 <= m /\ m < n ==> move (s m) (s (SUC m)))`;;

let ReachLemma = thm `;
  !p p'. reachable p p'  <=>  ?n.  reachableN p p' n
  by reachable, reachableN;
`;;

let reachableN_CLAUSES = thm `;
  ! p p'. (reachableN p p' 0  <=>  p = p') /\
  ! n. reachableN p p' (SUC n)  <=>  ? q. reachableN p q n  /\ move q p'

  proof
    let p p' be triple;
    consider s0 such that
    s0 = \m:num. p';
    reachableN p p' 0  <=>  p = p'     [0CLAUSE] by -, reachableN, LT, LE_0;
    ! n. reachableN p p' (SUC n)  ==>  ? q. reachableN p q n  /\ move q p'     [Imp1]
    proof
      let n be num;
      assume reachableN p p' (SUC n)     [H1];
      consider s such that
      s 0 = p /\ s (SUC n) = p' /\ !m. m < SUC n ==> move (s m) (s (SUC m))     [sDef] by H1, LE_0, reachableN;
      consider q such that q = s n;
    qed     by sDef, -, LE_0, reachableN, LT;
    ! n. (? q. reachableN p q n  /\ move q p')  ==>  reachableN p p' (SUC n)
    proof
      let n be num;
      assume ? q. reachableN p q n  /\ move q p';
      consider q such that
      reachableN p q n  /\ move q p'     [qExists] by -;
      consider s such that
      s 0 = p /\ s n = q /\ !m. m < n ==> move (s m) (s (SUC m))     [sDef] by -, reachableN, LT, LE_0;
      consider t such that
      t = \m. if m < SUC n then s m else p';
      t 0 = p /\ t (SUC n) = p' /\ !m. m < SUC n ==> move (t m) (t (SUC m))     [tProp] by qExists, sDef, -, LT_0, LT_REFL, LT, LT_SUC;
    qed     by -, reachableN, LT, LE_0;
  qed     by 0CLAUSE, Imp1, -;
`;;

let reachableInvariant = thm `;
  !p p':triple. reachable p p'  ==>
  oriented_area p = oriented_area p'

  proof
    !n. !p p'. reachableN p p' n  ==>  oriented_area p = oriented_area p'     by INDUCT_TAC THEN ASM_MESON_TAC[reachableN_CLAUSES; moveInvariant];
  qed     by -, ReachLemma;
`;;

let move2Cond = new_definition
  `move2Cond (A,B,C) (A',B',C')  <=>
  ~collinear {B,A,A'} /\ ~collinear {A',B,B'}   \/
  ~collinear {A,B,B'} /\ ~collinear {B',A,A'}`;;

let reachableN_Two = thm `;
  !P0 P2:triple. reachableN P0 P2 2 <=>
  ?P1. move P0 P1 /\ move P1 P2
  by ONE, TWO, reachableN_CLAUSES;
`;;

let reachableN_Three = thm `;
   !P0 P3:triple. reachableN P0 P3 3  <=>
   ?P1 P2. move P0 P1 /\ move P1 P2 /\ move P2 P3

   proof
     3 = SUC 2     by ARITH_RULE;
   qed     by -, reachableN_Two, reachableN_CLAUSES;
`;;

let reachableN_Four = thm `;
  !P0 P4:triple. reachableN P0 P4 4  <=>
  ?P1 P2 P3. move P0 P1 /\ move P1 P2 /\ move P2 P3 /\ move P3 P4

   proof
     4 = SUC 3     by ARITH_RULE;
  qed     by -, reachableN_Three, reachableN_CLAUSES;
`;;

let moveSymmetry = thm `;
  let A B C A' B' C' be real^2;
  assume move (A,B,C) (A',B',C')                                [H1];
  thus move (B,C,A) (B',C',A') /\ move (C,A,B) (C',A',B') /\
  move (A,C,B) (A',C',B') /\ move (B,A,C) (B',A',C') /\ move (C,B,A) (C',B',A')

  proof
    !A B C A':real^2. collinear {vec 0, C - B, A' - A}  ==>
    collinear {vec 0, B - C, A' - A}     by REWRITE_TAC[COLLINEAR_3_2Dzero] THEN VEC2_TAC;
  qed     by H1, -, move;
`;;

let reachableNSymmetry = thm `;
  ! A B C A' B' C' n. reachableN (A,B,C) (A',B',C') n  ==>
  reachableN (B,C,A) (B',C',A') n  /\  reachableN (C,A,B) (C',A',B') n /\
  reachableN (A,C,B) (A',C',B') n  /\  reachableN (B,A,C) (B',A',C') n /\
  reachableN (C,B,A) (C',B',A') n

  proof
    let A B C be real^2;
    consider Q such that Q = \n A' B' C'.
    reachableN (B,C,A) (B',C',A') n  /\  reachableN (C,A,B) (C',A',B') n /\
    reachableN (A,C,B) (A',C',B') n  /\  reachableN (B,A,C) (B',A',C') n /\
    reachableN (C,B,A) (C',B',A') n     [Qdef];
    consider P such that
    P = \n. ! A' B' C'. reachableN (A,B,C) (A',B',C') n  ==> Q n A' B' C'    [Pdef];
    P 0     [Base] by -, Qdef, reachableN_CLAUSES, PAIR_EQ;
    !n. P n ==> P (SUC n)
    proof
      let n be num;
      assume P n [Pn];
      ! A' B' C'. reachableN (A,B,C) (A',B',C') (SUC n)  ==> Q (SUC n) A' B' C'
      proof
        let A' B' C' be real^2;
        assume reachableN (A,B,C) (A',B',C') (SUC n);
        consider X Y Z such that
        reachableN (A,B,C) (X,Y,Z) n /\ move (X,Y,Z) (A',B',C')     [XYZdef] by -, reachableN_CLAUSES, PAIR_SURJECTIVE;
      qed     by -, Qdef, Pdef, Pn, XYZdef, moveSymmetry, reachableN_CLAUSES;
    qed     by -, Pdef;
    !n. P n     by Base, -, INDUCT_TAC;
  qed     by -, Pdef, Qdef;
`;;

let ORIENTED_AREA_COLLINEAR_CONG = thm `;
  let A B C A' B' C' be real^2;
  assume oriented_area (A,B,C) = oriented_area (A',B',C')               [H1];
  thus collinear {A,B,C} <=> collinear {A',B',C'}
  by     H1, REWRITE_TAC[COLLINEAR_3_2D; oriented_area] THEN CONV_TAC REAL_RING;
`;;

let Basic2move_THM = thm `;
  let A B C A' be real^2;
  assume ~collinear {A,B,C}                                     [H1];
  assume ~collinear {B,A,A'}                                    [H2];
  thus ? X. move (A,B,C) (A,B,X)  /\  move (A,B,X) (A',B,X)

  proof
    !r. r % (A - B) = (--r) % (B - A)  /\  r % (A - B) = r % (A - B) + &0 % (C - B)     [add0vector_mul] by VEC2_TAC;
    ~ ? r. A' - A = r % (A - B)     [H2'] by H2, COLLINEAR_3, COLLINEAR_LEMMA, -;
    consider r t such that
    A' - A = r % (A - B) + t % (C - B)     [rExists] by H1, COLLINEAR_3, Noncollinear_2Span;
    ~(t = &0)     [tNonzero] by -, add0vector_mul, H2';
    consider s X such that
    s = r / t  /\  X = C + s % (A - B)     [Xexists] by rExists;
    A' - A = (t * s) % (A - B) + t % (C - B)     by rExists, -, tNonzero, REAL_DIV_LMUL;
    A' - A = t % (X - B)     [tProp] by -, Xexists, VEC2_TAC;
    X - C = (-- s) % (B - A)     by -, Xexists, VEC2_TAC;
    collinear {vec 0,B - A,X - C}  /\  collinear {vec 0,X - B,A' - A}     by -, tProp, COLLINEAR_LEMMA;
  qed     by -, move;
`;;

let FourStepMoveAB = thm `;
  let A B C A' B' C' be real^2;
  assume ~collinear {A,B,C}                                             [H1];
  assume ~collinear {B,A,A'} /\ ~collinear {A',B,B'}                     [H2];
  thus ? X Y. move (A,B,C) (A,B,X)  /\  move (A,B,X) (A',B,X)  /\
  move (A',B,X) (A',B,Y)  /\  move (A',B,Y) (A',B',Y)

  proof
    consider X such that
    move (A,B,C) (A,B,X)  /\  move (A,B,X) (A',B,X)     [ABX] by H1, H2, -, Basic2move_THM;
    ~collinear {A,B,X} /\ ~collinear {A',B,X}     by H1, -, moveInvariant, ORIENTED_AREA_COLLINEAR_CONG;
    ~collinear {B,A',X}     by -, collinearSymmetry;
    consider Y such that
    move (B,A',X) (B,A',Y)  /\  move (B,A',Y) (B',A',Y)     by -, H2, Basic2move_THM;
    move (A',B,X) (A',B,Y)  /\  move (A',B,Y) (A',B',Y)     by -, moveSymmetry;
  qed     by -, ABX;
`;;

let FourStepMoveABBAreach = thm `;
  let A B C A' B' C' be real^2;
  assume ~collinear {A,B,C}                                     [H1];
  assume move2Cond (A,B,C) (A',B',C')                           [H2];
  thus ? Y. reachableN (A,B,C) (A',B',Y) 4

  proof
    cases     by H2, move2Cond;
    suppose ~collinear {B,A,A'} /\ ~collinear {A',B,B'};
  qed     by H1, -, FourStepMoveAB, reachableN_Four;
    suppose ~collinear {A,B,B'} /\ ~collinear {B',A,A'}     [Case2];
    ~collinear {B,A,C}     by H1, collinearSymmetry;
    consider X Y such that
    move (B,A,C) (B,A,X)  /\  move (B,A,X) (B',A,X)  /\
    move (B',A,X) (B',A,Y)  /\  move (B',A,Y) (B',A',Y)     by -,  Case2, FourStepMoveAB;
  qed     by -, moveSymmetry, reachableN_Four;
  end;
`;;

let NotMove2Impliescollinear = thm `;
  let A B C A' B' C' be real^2;
  assume ~collinear {A,B,C} /\ ~collinear {A',B',C'}             [H1];
  assume ~(A = A') /\ ~(B = B')                                  [H2];
  assume ~move2Cond (A,B,C) (A',B',C')                          [H3];
  thus collinear {A,B,A',B'}

  proof
    ~(A = B) /\ ~(A' = B')     [Distinct] by H1, Noncollinear_3ImpliesDistinct;
    {A,B,A',B'} SUBSET {A,A',B,B'}  /\  {A,B,A',B'} SUBSET {B,B',A',A}  /\
    {A,B,A',B'} SUBSET {A',B',B,A}     [set4symmetry] by SET_RULE;
    cases     by H3, move2Cond;
    suppose collinear {B,A,A'} /\ collinear {A,B,B'};
      collinear {A,B,A'} /\ collinear {A,B,B'}     by -, collinearSymmetry;
    qed     by Distinct, -, COLLINEAR_4_3;
    suppose collinear {B,A,A'} /\ collinear {B',A,A'};
      collinear {A,A',B} /\ collinear {A,A',B'}     by  -, collinearSymmetry;
      collinear {A,A',B,B'}     by H2, -, COLLINEAR_4_3;
    qed     by -, set4symmetry, COLLINEAR_SUBSET;
    suppose collinear {A',B,B'} /\ collinear {A,B,B'};
      collinear {B,B',A'} /\ collinear {B,B',A}     by  -, collinearSymmetry;
      collinear {B,B',A',A}     by H2, -, COLLINEAR_4_3;
    qed     by -, set4symmetry, COLLINEAR_SUBSET;
    suppose collinear {A',B,B'} /\ collinear {B',A,A'};
      collinear {A',B',B} /\ collinear {A',B',A}     by  -, collinearSymmetry;
      collinear {A',B',B,A}     by Distinct, -, COLLINEAR_4_3;
    qed     by -, set4symmetry, COLLINEAR_SUBSET;
  end;
`;;

let DistinctImplies2moveable = thm `;
  let A B C A' B' C' be real^2;
  assume ~collinear {A,B,C} /\ ~collinear {A',B',C'}                     [H1];
  assume ~(A = A') /\ ~(B = B') /\ ~(C = C')                              [H2];
  thus  move2Cond (A,B,C) (A',B',C') \/ move2Cond (B,C,A) (B',C',A')

  proof
    {A, B, B'} SUBSET {A, B, A', B'} /\ {B,B',C} SUBSET {B,C,B',C'}     [3subset4] by SET_RULE;
    ~collinear {B,C,A} /\ ~collinear {B',C',A'}     [H1'] by H1, collinearSymmetry;
    assume ~(move2Cond (A,B,C) (A',B',C') \/ move2Cond (B,C,A) (B',C',A'));
    ~move2Cond (A,B,C) (A',B',C')  /\  ~move2Cond (B,C,A) (B',C',A')     by -;
    collinear {A, B, A', B'} /\ collinear {B,C,B',C'}     by H1, H1', -, H2, NotMove2Impliescollinear;
    collinear {A, B, B'} /\ collinear {B,B',C}     by -, 3subset4, COLLINEAR_SUBSET;
    collinear {A, B, C}     by -, H2, COLLINEAR_3_TRANS;
  qed     by  -, H1;
`;;

let SameCdiffAB = thm `;
  let A B C A' B' C' be real^2;
  assume ~collinear {A,B,C} /\ ~collinear {A',B',C'}                     [H1];
  assume C = C' /\ ~(A = A') /\ ~(B = B')                                 [H2];
  thus ? Y. reachableN (A,B,C) (Y,B',C') 2  \/ reachableN (A,B,C) (A',B',Y) 4

  proof
    {B,B',A} SUBSET {A,B,A',B'}  /\  {A,B,C} SUBSET {B,B',A,C}     [easy_set] by SET_RULE;
    cases;
    suppose ~collinear {C,B,B'};
      consider X such that
      move (B,C,A) (B,C,X) /\ move (B,C,X) (B',C',X)     by H1, collinearSymmetry, -, H2, Basic2move_THM;
    qed     by -, reachableN_Two, reachableNSymmetry;
    suppose move2Cond (A,B,C) (A',B',C');
    qed     by H1, -, FourStepMoveABBAreach;
    suppose collinear {C,B,B'}  /\  ~move2Cond (A,B,C) (A',B',C');
      collinear {B,B',A} /\ collinear {B,B',C}     by H1, H2, -, NotMove2Impliescollinear, easy_set, COLLINEAR_SUBSET, collinearSymmetry;
    qed     by -, H2, COLLINEAR_4_3, easy_set, COLLINEAR_SUBSET, H1;
  end;
`;;

let FourMovesToCorrectTwo = thm `;
  let A B C A' B' C' be real^2;
  assume ~collinear {A,B,C} /\ ~collinear {A',B',C'}                     [H1];
  thus  ? n. n < 5 /\ ? Y. reachableN (A,B,C) (A',B',Y) n  \/
  reachableN (A,B,C) (A',Y,C') n  \/ reachableN (A,B,C) (Y,B',C') n

  proof
    ~collinear {B,C,A} /\ ~collinear {B',C',A'} /\ ~collinear {C,A,B} /\ ~collinear {C',A',B'}     [H1'] by H1, collinearSymmetry;
    0 < 5  /\  2 < 5  /\  3 < 5  /\  4 < 5     [easy_arith] by ARITH_RULE;
    cases;
    suppose A = A' /\ B = B' /\ C = C'  \/  A = A' /\ B = B' /\ ~(C = C')  \/
    A = A' /\ ~(B = B') /\ C = C'  \/  ~(A = A') /\ B = B' /\ C = C';
      reachableN (A,B,C) (A',B',C') 0  \/  reachableN (A,B,C) (A',B',C) 0  \/
      reachableN (A,B,C) (A',B,C') 0  \/  reachableN (A,B,C) (A,B',C') 0     by -, reachableN_CLAUSES;
    qed     by -, easy_arith;
    suppose A = A' /\ ~(B = B') /\ ~(C = C')  \/
    ~(A = A') /\ B = B' /\ ~(C = C')  \/  ~(A = A') /\ ~(B = B') /\ C = C';
    qed     by H1, H1', -, SameCdiffAB, reachableNSymmetry, easy_arith;
    suppose ~(A = A') /\ ~(B = B') /\ ~(C = C');
      move2Cond (A,B,C) (A',B',C') \/ move2Cond (B,C,A) (B',C',A')     by H1, -, DistinctImplies2moveable;
    qed     by H1, H1', -, FourStepMoveABBAreach, reachableNSymmetry, reachableN_Four, easy_arith;
  end;
`;;

let CorrectFinalPoint = thm `;
  let A B C A' C' be real^2;
  assume oriented_area (A,B,C) = oriented_area (A,B,C')         [H1];
  thus  move (A,B,C) (A,B,C')

  proof
    ((B$1 - A$1) * (C$2 - A$2) - (C$1 - A$1) * (B$2 - A$2)) / &2 =
    ((B$1 - A$1) * (C'$2 - A$2) - (C'$1 - A$1) * (B$2 - A$2)) / &2     by H1, oriented_area;
    (C$1 - C'$1) * (B$2 - A$2) = (B$1 - A$1) * (C$2 - C'$2)     by -, REAL_ARITH;
    (C' - C)$1 * (B - A)$2 = (B - A)$1 * (C' - C)$2     by -, VEC2_TAC;
    collinear {vec 0, B - A, C' - C}     by -, COLLINEAR_3_2Dzero;
  qed     by -, move;
`;;

let FiveMovesOrLess = thm `;
  let A B C A' B' C' be real^2;
  assume ~collinear {A,B,C}                                     [H1];
  assume oriented_area (A,B,C) = oriented_area (A',B',C')       [H2];
  thus  ? n. n <= 5 /\ reachableN (A,B,C) (A',B',C') n

  proof
     ~collinear {A',B',C'}     [H1'] by H1, H2, ORIENTED_AREA_COLLINEAR_CONG;
    ~(A = B) /\ ~(A = C) /\ ~(B = C) /\ ~(A' = B') /\ ~(A' = C') /\ ~(B' = C')     [Distinct] by H1, -,  Noncollinear_3ImpliesDistinct;
    consider n Y such that
    n < 5 /\ (reachableN (A,B,C) (A',B',Y) n \/
    reachableN (A,B,C) (A',Y,C') n \/ reachableN (A,B,C) (Y,B',C') n)     [2Correct] by H1, H1', FourMovesToCorrectTwo;
    cases     by 2Correct;
    suppose reachableN (A,B,C) (A',B',Y) n     [Case];
      oriented_area (A',B',Y) = oriented_area (A',B',C')     by H2, -, ReachLemma, reachableInvariant;
      move (A',B',Y) (A',B',C')     by -, Distinct, CorrectFinalPoint;
    qed by Case, -, reachableN_CLAUSES, 2Correct, LE_SUC_LT;
    suppose reachableN (A,B,C) (A',Y,C') n     [Case];
      oriented_area (A',C',Y) = oriented_area (A',C',B')     by H2, -, ReachLemma, reachableInvariant, oriented_areaSymmetry;
      move (A',Y,C') (A',B',C')     by -, Distinct, CorrectFinalPoint, moveSymmetry;
    qed by Case, -, reachableN_CLAUSES, 2Correct, LE_SUC_LT;
    suppose reachableN (A,B,C) (Y,B',C') n     [Case];
      oriented_area (B',C',Y) = oriented_area (B',C',A')     by H2, -, ReachLemma, reachableInvariant, oriented_areaSymmetry;
      move (Y,B',C') (A',B',C')     by -, Distinct, CorrectFinalPoint, moveSymmetry;
    qed     by Case, -, reachableN_CLAUSES, 2Correct, LE_SUC_LT;
  end;
`;;

let NOTENOUGH_4 = thm `;
  ?p0 p4. oriented_area p0 = oriented_area p4 /\ ~reachableN p0 p4 4

  proof
    consider p0 p4 such that
    p0 = vector [&0;&0]:real^2,vector [&0;&1]:real^2,vector [&1;&0]:real^2 /\
    p4 = vector [&1;&1]:real^2,vector [&1;&2]:real^2,vector [&2;&1]:real^2     [p04Def];
    oriented_area p0 = oriented_area p4     [equal_areas] by -, ASM_REWRITE_TAC[oriented_area] THEN VEC2_TAC;
    ~reachableN p0 p4 4     by p04Def, ASM_REWRITE_TAC[reachableN_Four; NOT_EXISTS_THM; FORALL_PAIR_THM; move; COLLINEAR_3_2Dzero; FORALL_VECTOR_2] THEN VEC2_TAC;
  qed     by equal_areas, -;
`;;

let reachableN_Five = thm `;
  !P0 P5:triple. reachableN P0 P5 5  <=>
  ?P1 P2 P3 P4. move P0 P1 /\ move P1 P2 /\ move P2 P3 /\ move P3 P4 /\ move P4 P5

  proof
    5 = SUC 4     by ARITH_RULE;
  qed by -, reachableN_CLAUSES, reachableN_Four;
`;;

let EasyCollinearMoves = thm `;
  (!A A' B:real^2. move (A:real^2,B,B) (A',B,B))  /\
  !A B B' C:real^2. collinear {A:real^2,B,C} /\ collinear {A,B',C}
  ==>  move (A,B,C) (A,B',C)
  by     REWRITE_TAC[move; COLLINEAR_3_2D] THEN VEC2_TAC;
`;;

let FiveMovesOrLess_STRONG = thm `;
  let A B C A' B' C' be real^2;
  assume oriented_area (A,B,C) = oriented_area (A',B',C')       [H1];
  thus ?n. n <= 5 /\ reachableN (A,B,C) (A',B',C') n

  proof
    {A,C,C} = {A,C}  /\  {B',C,C} = {B',C}  /\  {B',B',C} = {B',C}  /\  {B',B',C'} = {B',C'}     [easy_sets] by SET_RULE;
    cases;
    suppose ~collinear {A,B,C};
    qed     by -, H1, FiveMovesOrLess;
    suppose collinear {A,B,C}     [ABCcol];
      collinear {A',B',C'}     [A'B'C'col] by -, H1, ORIENTED_AREA_COLLINEAR_CONG;
      consider P1 P2 P3 P4 such that
      P1 = A,C,C  /\  P2 = B',C,C  /\  P3 = B',B',C  /\  P4 = B',B',C';
      move (A,B,C) P1  /\  move P1 P2  /\  move P2 P3  /\  move P3 P4  /\  move P4 (A',B',C')     by -, ABCcol, A'B'C'col, easy_sets, COLLINEAR_2, collinearSymmetry, moveSymmetry, EasyCollinearMoves;
    qed     by -, reachableN_Five, LE_REFL;
  end;
`;;
